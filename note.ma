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

include "arithmetics/nat.ma".
include "variable finite set.ma".

(*
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
*)
lemma leb_true_to_leb_S: ∀x,y. (leb x y)=true → (leb (S x) (S y))=true.
#x #y normalize // qed.

lemma leb_false_to_leb_S: ∀x,y. (leb x y)=false → (leb (S x) (S y))=false.
#x #y normalize // qed.

lemma leb_Sx_x: ∀x. leb (S x) x=false.
#x elim x normalize // qed.

lemma inverse: ∀P,Q. (P→ Q)→(¬ Q→ ¬P).
#P #Q #H #nq /3/ qed.
  
lemma foo_aux: ∀x, y. max (S x) (S y) = S (max x y).
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

lemma persistent_case: ∀n. n =0 ∨ ∃x. S x=n.
#n cases n
[ % //
| #m cut (∃x. S x= S m) /2/
] qed.