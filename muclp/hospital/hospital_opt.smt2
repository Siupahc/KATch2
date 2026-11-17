; Hospital example, "helped" pfwCSP encoding: same problem as hospital_bfs.smt2, with the
; structure of the problem pushed into the encoding so that PCSat has less to guess.
;
;   Internet -pt1-> G -2---1- S -2---1- M   (imaging, vulnerable FTP server)
;                             S -3---1- W   (workstation)
;                             S -4---1- I   (inspection)
;
; Packet = (sw pt dst typ dir);  sw, dst: G=1 S=2 M=3 W=4 I=5;  typ: ftp=21;  dir: in=0 out=1.
;
; Differences with hospital_bfs.smt2 (all sound, none loses the expected solution):
;  1. N3 + anti-spoofing are built into the shape of the hole: on S, X only chooses the
;     output port, so the unknown is X(pt, dst, typ, pt') instead of X(p, p') over 10 ints.
;  2. The known steps (Pol0, Link) are partial *functions*, so "exists a known step to a D
;     packet" is written with a universal (no existential, no skolem function); the only
;     existential left is the port chosen by X on S.
;  3. W is fixed by BFS distances (pdf section 5).
(set-logic HORN)

(declare-fun X (Int Int Int Int) Bool)          ; X pt dst typ pt'  (on S, dir in -> out)
(declare-fun R (Int Int Int Int Int) Bool)
(declare-fun D (Int Int Int Int Int) Bool)

(define-fun In ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (and (= s 1) (= p 1) (= r 0)))

(define-fun Legit ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (and (In s p d y r) (or (= d 4) (and (= d 3) (not (= y 21))))))

(define-fun Goal ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (and (= s d) (= r 0)))

(define-fun Link ((s Int) (p Int) (d Int) (y Int) (r Int)
                  (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int)) Bool
  (and (= r 1) (= r2 0) (= d2 d) (= y2 y)
       (or (and (= s 1) (= p 2) (= s2 2) (= p2 1))
           (and (= s 2) (= p 1) (= s2 1) (= p2 2))
           (and (= s 2) (= p 2) (= s2 3) (= p2 1))
           (and (= s 3) (= p 1) (= s2 2) (= p2 2))
           (and (= s 2) (= p 3) (= s2 4) (= p2 1))
           (and (= s 4) (= p 1) (= s2 2) (= p2 3))
           (and (= s 2) (= p 4) (= s2 5) (= p2 1))
           (and (= s 5) (= p 1) (= s2 2) (= p2 4)))))

(define-fun Pol0 ((s Int) (p Int) (d Int) (y Int) (r Int)
                  (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int)) Bool
  (and (= r 0) (= r2 1) (= s2 s) (= d2 d) (= y2 y)
       (or (and (= s 1) (= p2 2))
           (and (= s 5) (= p2 1)))))

(define-fun Known ((s Int) (p Int) (d Int) (y Int) (r Int)
                   (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int)) Bool
  (or (Pol0 s p d y r s2 p2 d2 y2 r2) (Link s p d y r s2 p2 d2 y2 r2)))

; Known has a successor from p (Pol0 on G/I in, or a link out of a wired port)
(define-fun HasKnown ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (or (and (= r 0) (or (= s 1) (= s 5)))
      (and (= r 1) (or (and (= s 1) (= p 2))
                       (and (= s 2) (>= p 1) (<= p 4))
                       (and (>= s 3) (<= s 5) (= p 1))))))

(define-fun Dist ((s Int) (d Int)) Int
  (ite (= s d) 0 (ite (or (= s 2) (= d 2)) 1 2)))

(define-fun Rank ((s Int) (r Int) (d Int)) Int
  (- (* 2 (Dist s d)) r))

; ---------- N2: FTP never reaches M ----------

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (In s p d y r) (R s p d y r))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int)
                 (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
  (=> (and (R s p d y r) (Known s p d y r s2 p2 d2 y2 r2))
      (R s2 p2 d2 y2 r2))))

(assert (forall ((p Int) (d Int) (y Int) (p2 Int))
  (=> (and (R 2 p d y 0) (X p d y p2))
      (R 2 p2 d y 1))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (and (R s p d y r) (= s 3) (= y 21)) false)))

; ---------- N1: legit traffic gets delivered ----------

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (Legit s p d y r) (D s p d y r))))

; off S (or on S going out): the known step must exist and lead closer, to a D packet
(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (and (D s p d y r) (not (Goal s p d y r)) (not (and (= s 2) (= r 0))))
      (HasKnown s p d y r))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int)
                 (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
  (=> (and (D s p d y r) (not (Goal s p d y r)) (not (and (= s 2) (= r 0)))
           (Known s p d y r s2 p2 d2 y2 r2))
      (and (D s2 p2 d2 y2 r2)
           (<= 0 (Rank s2 r2 d2)) (< (Rank s2 r2 d2) (Rank s r d))))))

; on S coming in: X must pick some output port leading closer, to a D packet
(assert (forall ((p Int) (d Int) (y Int))
  (=> (and (D 2 p d y 0) (not (Goal 2 p d y 0)))
      (exists ((p2 Int))
        (and (X p d y p2) (D 2 p2 d y 1)
             (<= 0 (Rank 2 1 d)) (< (Rank 2 1 d) (Rank 2 0 d)))))))

(check-sat)
