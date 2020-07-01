(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/bool.ma".
include "basics/logic.ma".
include "arithmetics/nat.ma".
include "basics/deqsets.ma".
include "basics/finset.ma".
include "crumbles.ma".

let rec neqb n m ≝
 match n with
 [ O ⇒ match m with
       [ O ⇒ true
       | S q ⇒ false
       ]
 |S p ⇒ match m with
       [ O ⇒ false
       | S q ⇒ neqb p q]].

lemma rifle_neqb: ∀n. neqb n n= true.
#n elim n[//|#x #Hind normalize assumption]. qed.

lemma neq_simm: ∀x, y. (neqb x y = neqb y x).
#x elim x [ #y elim y [//| #y #H normalize //] | #x1 #H1 #y elim y [normalize // | #y1 #H normalize @H1 ] ] qed.

lemma neqb_false: ∀x. neqb x (S x) =false.
#x elim x [// | #y #Hind normalize @Hind].qed.

lemma neqb_false1: ∀x. neqb (S x) x =false.
#x elim x [// | #y #Hind normalize @Hind].qed.

lemma neqb_iff_eq: ∀n, m. neqb n m = true ↔ n=m.
#n elim n
 [*
  [ /2/
  | #m normalize %
   [ #abs destruct
   | #abs destruct
   ]
  ]
 | #p #IH *
  [ normalize % #abs destruct
   | #q normalize %
    [ cases (IH q) #H8 #H9 #H10 cut (p=q)
     [ cut (neqb p q = true)
      [ assumption
      | assumption
      ]
     | #H11 //
     ]
    | #H cut (p=q)
      [ //
      | #H >H //]
      ]
     ] qed.

let rec veqb (n: Variable) (m: Variable) ≝
 match n with
 [ variable n1 ⇒ match m with [ variable m1 ⇒ neqb n1 m1 ] ].

lemma eq_to_veq: ∀a, b: Variable. a=b → (veqb a b = true).
#a #b #H destruct cases b #n cases n //#m normalize // qed.

lemma aux: ∀a, b: nat. veqb (variable a) (variable b)= true → neqb a b = true.
#na
#nb
cases na
cases nb
[ //
| #n normalize #H destruct
| #n normalize //
| #n normalize #m #J @J
]
qed.

lemma var_n: ∀a, b. veqb (variable a) (variable b) = neqb a b.
#a elim a
 [ * //
 | #pa #Hind *
  [ normalize //
  | #pb normalize //
  ]
 ]
qed.

lemma var_m: ∀a, b. variable a =variable b ↔ a=b.
*
[ * normalize
 [ % //
 | #m % #H destruct
 ]
| #p #q %
 [ #aux destruct // ]
#p destruct // qed.


theorem veqb_true_to_eq: ∀a,b: Variable. (veqb a b=true)↔(a=b).
#a #b cases a cases b #na #nb >var_n normalize % #H [ cases (var_m na nb) #H1 #H2 cases (var_n na nb)
lapply H cases (neqb_iff_eq na nb) #H29 #H30 #H31 cut (na =nb) cut (neqb nb na =true) // /2/
| cases (aux na nb) /2/ qed.

lemma not_gt_to_le: ∀x,y. x ≯y → x ≤y.
#x #y #H normalize in H; /3/ qed.

lemma le_to_not_gt: ∀x,y. x ≤y → x ≯y.
#x #y #H normalize in H; normalize /3/ qed.

lemma not_ge_1_to_O: ∀x. 1≰x → x=0.
#x cases x normalize [#_ // | #n #Abs @False_ind normalize in Abs; /2/] qed.

lemma not_le_to_lt: ∀x,y. x ≰ y → y < x.
#x #y /2/ qed.

lemma succ_eq: ∀n, m:nat. S n = S m → n = m.
#n #m #H destruct // qed.

lemma subtr_1: ∀a,b,c:nat. a+b-(a+c)=b-c.
#a #b #c elim a // qed.

lemma leq1: ∀a, b, c.∀P:Prop. a≤b → (a ≤ b+c → P )→ P.
#a #b #c #P #H1 #H2 cut (b≤b+c)
 [ // |  #H3 cut (a≤b+c) [ @(transitive_le ? (b)) // | #H4 @(H2 H4)]] qed.

lemma le_plus_a_r: ∀a,n,m. n ≤ m → n ≤ m + a.
/2/ qed.

lemma le_aux1: ∀a, b. leb a b = false → b < a.
#a #b #H lapply (leb_false_to_not_le … H) #H @(not_le_to_lt … H) qed.

lemma le_aux2: ∀m: nat. ∀P: Prop. ((0 ≤ m) → P) → P.
#m #P #H cut (∀n. 0≤n) [ #n cases n //| #H1 @(H (H1 m))] qed.

lemma max_O: ∀x. max x O = x.
#x cases x //. qed.

lemma and_true: ∀x. (x ∧ true) = x.
#x cases x // qed.

lemma or_false: ∀x. (x ∨ false) = x.
#x cases x // qed.

lemma max_n_m: ∀n,m. max n m =n ∨ max n m = m.
#n #m cases n [ normalize //| cases m #nn
 [ normalize /2/ | #mm normalize cases (leb mm nn) normalize /2/] qed.

lemma if_leb_x_O: ∀x. if (leb x O) then O else x =x.
#x cases x normalize [// |#m //] qed.

lemma lt_to_le: ∀n, m. n<m → n ≤ m.
/2/ qed.

lemma if_t: ∀A.∀x:A.∀y:A. if true then x else y = x.
#A #x #y normalize // qed.

lemma if_f: ∀A.∀x:A.∀y:A. if false then x else y = y.
#A #x #y normalize // qed.
