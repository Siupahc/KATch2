//! Reduce an SPP given a set of assumptions
//!
//! Input: a target SPP, and an SPP encoding the set of outputs we care about
//!
//! (Equivalently, it is the opposite of the don't-care set.)
//!
//! Output: a new SPP, hopefully smaller than input, with the goal that
//!
//! ```text
//! intersect(output, care) == intersect(target, care)
//! ```
//!
//! This is the BDD restrict algorithm (Coudert & Madre), adapted to SPPs.
//!
//! In a BDD, restrict simplifies a node by dropping it: when the care set only lives on one branch,
//! the node is replaced by that branch. SPPs never skip levels, so instead we pick the simplest
//! *shape* of node that is consistent with the care set. From simplest to most general:
//!
//!  1. Identity: `x00 == x11`, and `x01`, `x10` are zero (the bit is left alone, like `skip`).
//!  2. Assign 1: `x01 == x11`, and `x00`, `x10` are zero (like `x := 1`).
//!  3. Assign 0: `x00 == x10`, and `x01`, `x11` are zero (like `x := 0`).
//!  4. Havoc: all four children are equal (the bit is ignored and set to anything).
//!  5. Test: `x01`, `x10` are zero, but `x00` and `x11` may differ.
//!  6. General: each child is restricted on its own, and don't-care children become zero.
//!
//! Assignments come before havoc: both have a single child, but an assignment relates fewer packets
//! and is a smaller NetKAT term (`x := 1` rather than `x := 0 + x := 1`).
//!
//! Shapes 1 to 4 merge several children into one. The merged child must agree with each original
//! child on that child's care set, so it is the restriction of the union of the cared-about parts,
//! over the union of the care sets. This is feasible exactly when the children agree wherever their
//! care sets overlap. This merging is the SPP analogue of BDD restrict's "replace the node by one of
//! its children" step.

use crate::spp::{self, SPP};
use std::collections::HashMap;

pub fn reduce(store: &mut spp::SPPstore, target: SPP, care: SPP) -> SPP {
    let mut zeros = vec![SPP::new(0)];
    for _ in 0..store.num_vars() {
        let z = *zeros.last().unwrap();
        zeros.push(store.mk(z, z, z, z));
    }
    let mut reducer = Reducer {
        store,
        zeros,
        memo: HashMap::new(),
    };
    let depth = reducer.store.num_vars() as usize;
    reducer.reduce(target, care, depth)
}

struct Reducer<'a> {
    store: &'a mut spp::SPPstore,
    /// `zeros[d]` is the empty relation on `d` fields.
    zeros: Vec<SPP>,
    memo: HashMap<(SPP, SPP), SPP>,
}

impl Reducer<'_> {
    /// `target` and `care` are SPPs on `depth` fields.
    fn reduce(&mut self, target: SPP, care: SPP, depth: usize) -> SPP {
        if care == self.zeros[depth] {
            // Nothing is cared about, so the simplest answer will do.
            return self.zeros[depth];
        }
        if depth == 0 {
            // `care` is one, so we must keep `target` exactly.
            return target;
        }
        if let Some(&result) = self.memo.get(&(target, care)) {
            return result;
        }

        let t = self.store.get(target);
        let c = self.store.get(care);
        let ts = [t.x00, t.x01, t.x10, t.x11];
        let cs = [c.x00, c.x01, c.x10, c.x11];
        let zero = self.zeros[depth - 1];

        // Whether each child may be replaced by zero, i.e. it is zero everywhere we care about.
        let zero_children: [bool; 4] =
            [0, 1, 2, 3].map(|i| self.store.intersect(ts[i], cs[i]) == zero);
        let can_zero = |idxs: &[usize]| idxs.iter().all(|&i| zero_children[i]);

        let result = if let Some(r) = can_zero(&[1, 2])
            .then(|| self.merge(&ts, &cs, &[0, 3], depth - 1))
            .flatten()
        {
            // 1. Identity
            self.store.mk(r, zero, zero, r)
        } else if let Some(r) = can_zero(&[0, 2])
            .then(|| self.merge(&ts, &cs, &[1, 3], depth - 1))
            .flatten()
        {
            // 2. Assign 1
            self.store.mk(zero, r, zero, r)
        } else if let Some(r) = can_zero(&[1, 3])
            .then(|| self.merge(&ts, &cs, &[0, 2], depth - 1))
            .flatten()
        {
            // 3. Assign 0
            self.store.mk(r, zero, r, zero)
        } else if let Some(r) = self.merge(&ts, &cs, &[0, 1, 2, 3], depth - 1) {
            // 4. Havoc
            self.store.mk(r, r, r, r)
        } else if can_zero(&[1, 2]) {
            // 5. Test
            let r00 = self.reduce(ts[0], cs[0], depth - 1);
            let r11 = self.reduce(ts[3], cs[3], depth - 1);
            self.store.mk(r00, zero, zero, r11)
        } else {
            // 6. General
            let [r00, r01, r10, r11] = [0, 1, 2, 3].map(|i| {
                if zero_children[i] {
                    zero
                } else {
                    self.reduce(ts[i], cs[i], depth - 1)
                }
            });
            self.store.mk(r00, r01, r10, r11)
        };

        self.memo.insert((target, care), result);
        result
    }

    /// Try to find a single SPP that agrees with `ts[i]` on `cs[i]` for every `i` in `idxs`.
    ///
    /// Returns `None` if two of the children disagree somewhere both are cared about.
    fn merge(&mut self, ts: &[SPP; 4], cs: &[SPP; 4], idxs: &[usize], depth: usize) -> Option<SPP> {
        let mut merged_target = self.zeros[depth];
        let mut merged_care = self.zeros[depth];
        for &i in idxs {
            let cared = self.store.intersect(ts[i], cs[i]);
            merged_target = self.store.union(merged_target, cared);
            merged_care = self.store.union(merged_care, cs[i]);
        }
        // `merged_target` contains each child's cared-about part; check it adds nothing extra.
        for &i in idxs {
            let restricted = self.store.intersect(merged_target, cs[i]);
            let cared = self.store.intersect(ts[i], cs[i]);
            if restricted != cared {
                return None;
            }
        }
        Some(self.reduce(merged_target, merged_care, depth))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(store: &mut spp::SPPstore, target: SPP, care: SPP) -> SPP {
        let result = reduce(store, target, care);
        let lhs = store.intersect(result, care);
        let rhs = store.intersect(target, care);
        assert_eq!(
            lhs, rhs,
            "reduce({target}, {care}) = {result} disagrees on the care set"
        );
        result
    }

    #[test]
    fn exhaustive_one_field() {
        let mut store = spp::SPPstore::new(1);
        let all = store.all();
        for &target in &all {
            for &care in &all {
                check(&mut store, target, care);
            }
        }
    }

    #[test]
    fn random_agrees_on_care_set() {
        for n in 2..=4 {
            let mut store = spp::SPPstore::new(n);
            for _ in 0..500 {
                let target = store.rand();
                let care = store.rand();
                check(&mut store, target, care);
            }
        }
    }

    #[test]
    fn simple_cases() {
        let mut store = spp::SPPstore::new(3);
        let (zero, one, top) = (store.zero, store.one, store.top);
        let t = store.test(1, true);

        // Caring about everything changes nothing
        assert_eq!(check(&mut store, t, top), t);
        // Caring about nothing gives zero
        assert_eq!(check(&mut store, t, zero), zero);
        // Caring only about the identity part of top gives identity
        assert_eq!(check(&mut store, top, one), one);
        assert_eq!(check(&mut store, one, one), one);
        // A test, if we only care where it passes, is the identity
        assert_eq!(check(&mut store, t, t), one);
        // An assignment stays an assignment, even if we only care about some inputs
        let assign = store.assign(1, true);
        assert_eq!(check(&mut store, assign, top), assign);
        let t0 = store.test(0, false);
        let care = store.sequence(t0, top);
        assert_eq!(check(&mut store, assign, care), assign);
    }
}
