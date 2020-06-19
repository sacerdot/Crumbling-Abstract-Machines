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

record DeqSet: Type[1] ≝ 
{ carr: >Type[0]
; eqb: carr → carr → bool
; eqb_true: ∀x,y. (eqb x y=true)↔(x=y)
}.

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

definition DeqVar ≝ mk_DeqSet Variable veqb veqb_true_to_eq.
