; Hospital example (hospital_test.pdf, section 4) as a pfwCSP for PCSat.
;
;   Internet -pt1-> G -2---1- S -2---1- M   (imaging, vulnerable FTP server)
;                             S -3---1- W   (workstation)
;                             S -4---1- I   (inspection)
;
; A packet is 5 integers (sw pt dst typ dir):
;   sw, dst : G=1  S=2  M=3  W=4  I=5
;   typ     : ftp=21, anything else = not ftp
;   dir     : in=0  out=1     (policy step: in -> out, link step: out -> in)
;
; Unknowns: X (the hole = policy of S), R (safety invariant), D (packets that will be
; delivered), W (well-founded progress relation).  This variant leaves W free.
(set-logic HORN)

(declare-fun  X (Int Int Int Int Int  Int Int Int Int Int) Bool)
(declare-fun  R (Int Int Int Int Int) Bool)
(declare-fun  D (Int Int Int Int Int) Bool)
(declare-wfp  W (Int Int Int Int Int  Int Int Int Int Int) Bool)

; ---------- known parts of the network ----------

; In(p): packets entering from the Internet at G, port 1
(define-fun In ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (and (= s 1) (= p 1) (= r 0)))

; Legit(p): entering packets for W, or for M and not FTP  (N1)
(define-fun Legit ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (and (In s p d y r) (or (= d 4) (and (= d 3) (not (= y 21))))))

; Goal(p): the packet arrived at its destination
(define-fun Goal ((s Int) (p Int) (d Int) (y Int) (r Int)) Bool
  (and (= s d) (= r 0)))

; Link(p, p'): the topology t, 8 directed links, out -> in
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

; Pol0(p, p'): fixed policies, G sends out on port 2, I sends out on port 1, in -> out
(define-fun Pol0 ((s Int) (p Int) (d Int) (y Int) (r Int)
                  (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int)) Bool
  (and (= r 0) (= r2 1) (= s2 s) (= d2 d) (= y2 y)
       (or (and (= s 1) (= p2 2))
           (and (= s 5) (= p2 1)))))

(define-fun Known ((s Int) (p Int) (d Int) (y Int) (r Int)
                   (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int)) Bool
  (or (Pol0 s p d y r s2 p2 d2 y2 r2) (Link s p d y r s2 p2 d2 y2 r2)))

; ---------- N2: FTP never reaches M (R = reachability invariant) ----------

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (In s p d y r) (R s p d y r))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int)
                 (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
  (=> (and (R s p d y r) (Known s p d y r s2 p2 d2 y2 r2))
      (R s2 p2 d2 y2 r2))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int)
                 (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
  (=> (and (R s p d y r) (= s 2) (= r 0) (X s p d y r s2 p2 d2 y2 r2))
      (R s2 p2 d2 y2 r2))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (and (R s p d y r) (= s 3) (= y 21)) false)))

; ---------- N1: legit traffic gets delivered (D + exists p' + W) ----------

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (Legit s p d y r) (D s p d y r))))

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int))
  (=> (and (D s p d y r) (not (Goal s p d y r)))
      (exists ((s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
        (and (or (Known s p d y r s2 p2 d2 y2 r2)
                 (and (= s 2) (= r 0) (X s p d y r s2 p2 d2 y2 r2)))
             (D s2 p2 d2 y2 r2)
             (W s p d y r s2 p2 d2 y2 r2))))))

; ---------- N3: S just forwards (no teleport) ----------

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int)
                 (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
  (=> (X s p d y r s2 p2 d2 y2 r2)
      (and (= s2 s) (= r2 1)))))

; ---------- Step 7 (optional): anti-spoofing ----------

(assert (forall ((s Int) (p Int) (d Int) (y Int) (r Int)
                 (s2 Int) (p2 Int) (d2 Int) (y2 Int) (r2 Int))
  (=> (X s p d y r s2 p2 d2 y2 r2)
      (and (= y2 y) (= d2 d)))))

(check-sat)
