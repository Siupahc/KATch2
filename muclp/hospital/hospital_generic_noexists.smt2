; =============================================================================
;  Lower star with explicit cable branches and no integer witnesses.
;  Derived from the generic hospital encoding in the note
;  "NetKAT synthesis to pfwCSP: the generic translation" to
;
;    N2:  in ; (pol[X] ; link)* ; out ; sw=M ; typ=ftp  <=  0
;    N1:  spec  <=  in ; (pol[X] ; link)* ; out
;    N3:  X  <=  sw=S ; T ; sw:=S
;
;  Packet = 4 integers (sw pt dst typ).  G=1 S=2 M=3 W=4 I=5, ftp=21.
;  Variables:  p = (sw pt dst typ)        q = (sw_q ...)   intermediate
;              r = (sw_r ...) intermediate  p' = (sw2 pt2 dst2 typ2)
;
;  Run:  main.exe -c <pcsat config> -p pfwcsp hospital_generic_noexists.smt2
; =============================================================================
(set-logic HORN)

(define-fun G () Int 1) (define-fun S () Int 2) (define-fun M () Int 3)
(define-fun W () Int 4) (define-fun I () Int 5) (define-fun FTP () Int 21)

; ---- hole-free, star-free terms: plain formulas (the "exists q" of ';' is
; ---- eliminated by substitution, see section 5 of the note) ----------------

; T(1): identity
(define-fun Eq ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int)) Bool
  (and (= sw2 sw) (= pt2 pt) (= dst2 dst) (= typ2 typ)))

; T(sw=a ; pt=i ; sw:=b ; pt:=j): one direction of one link
(define-fun cable ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int) (a Int) (i Int) (b Int) (j Int)) Bool
  (and (= sw a) (= pt i) (= sw2 b) (= pt2 j) (= dst2 dst) (= typ2 typ)))

; T(t): the topology, a sum of 8 cables
(define-fun Link ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int)) Bool
  (or (cable sw pt dst typ sw2 pt2 dst2 typ2 G 2 S 1) (cable sw pt dst typ sw2 pt2 dst2 typ2 S 1 G 2)
      (cable sw pt dst typ sw2 pt2 dst2 typ2 S 2 M 1) (cable sw pt dst typ sw2 pt2 dst2 typ2 M 1 S 2)
      (cable sw pt dst typ sw2 pt2 dst2 typ2 S 3 W 1) (cable sw pt dst typ sw2 pt2 dst2 typ2 W 1 S 3)
      (cable sw pt dst typ sw2 pt2 dst2 typ2 S 4 I 1) (cable sw pt dst typ sw2 pt2 dst2 typ2 I 1 S 4)))

; T(sw=G ; pt:=2  +  sw=I ; pt:=1): the fixed policies
(define-fun Pol0 ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int)) Bool
  (and (= sw2 sw) (= dst2 dst) (= typ2 typ)
       (or (and (= sw G) (= pt2 2)) (and (= sw I) (= pt2 1)))))

; the tests in, out
(define-fun In  ((sw Int) (pt Int)) Bool (and (= sw G) (= pt 1)))
(define-fun Out ((sw Int)) Bool (or (= sw M) (= sw W)))

; T(spec) = T(in ; (dst=W ; sw:=W  +  dst=M ; typ!=ftp ; sw:=M))
(define-fun Spec ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int)) Bool
  (and (In sw pt) (= pt2 pt) (= dst2 dst) (= typ2 typ)
       (or (and (= dst W) (= sw2 W))
           (and (= dst M) (not (= typ FTP)) (= sw2 M)))))

; ---- unknowns ---------------------------------------------------------------
(declare-fun X  (Int Int Int Int Int Int Int Int) Bool)   ; the hole:  X(p, p')
(declare-fun St (Int Int Int Int Int Int Int Int) Bool)   ; star on the LEFT  of <= (over-approx.)
(declare-fun D  (Int Int Int Int Int Int Int Int) Bool)   ; star on the RIGHT of <= (under-approx.)
(declare-wfp W_ (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)  ; progress for D:  W_((p,p'), (r,p'))

; ---- star on the left: St contains (pol[X] ; link)* --------------------------
; (St-0)  1 <= St
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int))
  (St sw pt dst typ sw pt dst typ)))

; (St-1)  St ; pol[X] ; link <= St     -- split on the '+' of pol[X]: known part
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw_r Int) (pt_r Int) (dst_r Int) (typ_r Int) (sw_q Int) (pt_q Int) (dst_q Int) (typ_q Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (and (St sw pt dst typ sw_r pt_r dst_r typ_r) (Pol0 sw_r pt_r dst_r typ_r sw_q pt_q dst_q typ_q) (Link sw_q pt_q dst_q typ_q sw2 pt2 dst2 typ2))
      (St sw pt dst typ sw2 pt2 dst2 typ2))))

; (St-2)  same, hole part  (sw=S ; X)
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw_r Int) (pt_r Int) (dst_r Int) (typ_r Int) (sw_q Int) (pt_q Int) (dst_q Int) (typ_q Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (and (St sw pt dst typ sw_r pt_r dst_r typ_r) (= sw_r S) (X sw_r pt_r dst_r typ_r sw_q pt_q dst_q typ_q) (Link sw_q pt_q dst_q typ_q sw2 pt2 dst2 typ2))
      (St sw pt dst typ sw2 pt2 dst2 typ2))))

; ---- N2:  T+(in ; star ; out ; sw=M ; typ=ftp)(p,p')  =>  false --------------
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (and (In sw pt) (St sw pt dst typ sw2 pt2 dst2 typ2) (Out sw2) (= sw2 M) (= typ2 FTP))
      false)))

; ---- D step specialized using Link, Pol0, N3 and the anti-spoofing clause ----
; Enumerate the four outgoing cables of S.
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (D sw pt dst typ sw2 pt2 dst2 typ2)
      (or (Eq sw pt dst typ sw2 pt2 dst2 typ2)
          (and (= sw G)
                 (D S 1 dst typ sw2 pt2 dst2 typ2)
                 (W_ sw pt dst typ sw2 pt2 dst2 typ2 S 1 dst typ sw2 pt2 dst2 typ2))
          (and (= sw I)
                 (D S 4 dst typ sw2 pt2 dst2 typ2)
                 (W_ sw pt dst typ sw2 pt2 dst2 typ2 S 4 dst typ sw2 pt2 dst2 typ2))
          (and (= sw S) (X sw pt dst typ S 1 dst typ)
                 (D G 2 dst typ sw2 pt2 dst2 typ2)
                 (W_ sw pt dst typ sw2 pt2 dst2 typ2 G 2 dst typ sw2 pt2 dst2 typ2))
          (and (= sw S) (X sw pt dst typ S 2 dst typ)
                 (D M 1 dst typ sw2 pt2 dst2 typ2)
                 (W_ sw pt dst typ sw2 pt2 dst2 typ2 M 1 dst typ sw2 pt2 dst2 typ2))
          (and (= sw S) (X sw pt dst typ S 3 dst typ)
                 (D W 1 dst typ sw2 pt2 dst2 typ2)
                 (W_ sw pt dst typ sw2 pt2 dst2 typ2 W 1 dst typ sw2 pt2 dst2 typ2))
          (and (= sw S) (X sw pt dst typ S 4 dst typ)
                 (D I 1 dst typ sw2 pt2 dst2 typ2)
                 (W_ sw pt dst typ sw2 pt2 dst2 typ2 I 1 dst typ sw2 pt2 dst2 typ2))))))

; ---- N1:  T(spec)(p,p')  =>  T-(in ; star ; out)(p,p') -----------------------
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (Spec sw pt dst typ sw2 pt2 dst2 typ2)
      (and (In sw pt) (D sw pt dst typ sw2 pt2 dst2 typ2) (Out sw2)))))

; ---- N3:  X(p,p')  =>  T(sw=S ; T ; sw:=S)(p,p') -----------------------------
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (X sw pt dst typ sw2 pt2 dst2 typ2)
      (and (= sw S) (= sw2 S)))))

; ---- anti-spoofing (not in the paper's Ex. 2; comment out to match it) -------
; X <= (any rewrite of pt only)
(assert (forall ((sw Int) (pt Int) (dst Int) (typ Int) (sw2 Int) (pt2 Int) (dst2 Int) (typ2 Int))
  (=> (X sw pt dst typ sw2 pt2 dst2 typ2)
      (and (= dst2 dst) (= typ2 typ)))))

(check-sat)
