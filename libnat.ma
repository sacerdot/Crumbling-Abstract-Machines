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

lemma leq_zero: ∀n. S n ≤ O → False.
#n elim n normalize [/2/ | #m #H /2/] qed.

lemma leb_Sx_x: ∀x. leb (S x) x=false.
#x elim x normalize // qed.

lemma inverse: ∀P,Q. (P→ Q)→(¬ Q→ ¬P).
#P #Q #H #nq /3/ qed.

lemma neqb_x_max_Sx: ∀x,y. neqb x (max (S x) y)= false.
#x #y cut (leb x y = true ∨ leb x y = false) // * #Hleb normalize
change with (leb (S ?) ?) in match (match y in nat return λ_:ℕ.bool with [O⇒false|S (q:ℕ)⇒leb x q]);
cut (leb (S x) y= true ∨ leb (S x) y = false) // * #Hleb2
[ >Hleb2 normalize cut (x < y) [/3/ | #H  cut (x ≠ y) /3/ -H #H lapply (neqb_iff_eq x y) *
  #H1 #_ lapply(inverse … H1) #Hinv lapply (Hinv H) cases neqb /2/]
| cut (x=y)
 [ lapply (leb_true_to_le … Hleb) lapply(leb_false_to_not_le … Hleb2)#H1 #H2 cut (y ≤ x)
   [ lapply (not_le_to_lt … H1) /2/
   |#H3 /2/
   ]
 | #Heq destruct >(leb_Sx_x y) normalize /2/
 ]
| @False_ind lapply (leb_false_to_not_le … Hleb) lapply(leb_true_to_le … Hleb2) #H1 #H2 /3/
| >Hleb2 normalize /2/
] qed.

lemma leb_true_to_leb_S: ∀x,y. (leb x y)=true → (leb (S x) (S y))=true.
#x #y normalize // qed.

lemma leb_false_to_leb_S: ∀x,y. (leb x y)=false → (leb (S x) (S y))=false.
#x #y normalize // qed.

lemma max_S: ∀x, y. max (S x) (S y) = S (max x y).
#x elim x
[ #y normalize //
| #nx #H #y whd in match (max ? ?) in ⊢ %;
  change with (S (if leb (S nx) y then y else (S nx))) in match (S (max (S nx) y)) in ⊢ %;
  cut (leb (S nx) y=true ∨ (leb (S nx) y)=false) // * #Htf
  [ lapply (leb_true_to_leb_S … Htf)  #Hwow >Hwow >Htf normalize //
  | lapply (leb_false_to_leb_S … Htf)  #Hwow >Hwow >Htf normalize //
  ]
]
qed.

lemma max_swap: ∀x,y,z. max x (max y z)= max y (max x z).
#x elim x // #nx #Hx #y #z cases y cases z // qed.

lemma max_comm_aux1: ∀x, y. leb x y= false → eqb x y = false → leb y x = true.
#x #y #H1 #H2 lapply (leb_false_to_not_le … H1) -H1 #H1
 lapply (eqb_false_to_not_eq … H2) -H2 #H2 cut (y ≤x)
 [ /3/  | #Hf /2/] qed.

lemma max_comm_aux2: ∀x, y. leb x y= true → eqb x y = false → leb y x = false.
#x #y #H1 #H2 lapply (leb_true_to_le … H1) -H1 #H1
 lapply (eqb_false_to_not_eq … H2) -H2 #H2 cut (y ≰ x)
 [ /3/  | #Hf /2/] qed.


lemma max_comm: ∀x, y. max x y = max y x.
#x elim x
[ normalize #y cases y //
| #nx #H #y whd in match (max ? ?);
  whd in match (max y (S nx));
  cut (eqb (S nx) y = true ∨ eqb (S nx) y = false) // * #Heq
  [ lapply(eqb_true_to_eq … Heq) -Heq #Heq destruct //
  | cut (leb (S nx) y = true ∨ leb (S nx) y = false) // * #Hleb
   [ lapply (max_comm_aux2 … Hleb Heq) #Hwow >Hleb >Hwow normalize //
   | lapply (max_comm_aux1 … Hleb Heq) #Hwow >Hleb >Hwow normalize //
   ]
  ]
]
qed.

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
