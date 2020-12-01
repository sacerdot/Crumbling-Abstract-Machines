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

let rec gtb n m on n ≝
 match n with
 [ O ⇒ false
 | S n' ⇒ match m with [ O ⇒ true | S m' ⇒ gtb n' m']
 ]
.

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

lemma leq_to_geq: ∀x,y. x ≤ y → y ≥ x.
#x #y #H // qed.

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

(*lemma lt_to_le: ∀n, m. n<m → n ≤ m.
/2/ qed.
*)
lemma if_t: ∀A.∀x:A.∀y:A. if true then x else y = x.
#A #x #y normalize // qed.

lemma if_f: ∀A.∀x:A.∀y:A. if false then x else y = y.
#A #x #y normalize // qed.

lemma not_gt_lt: ∀n, m. n>m → n ≤ m → False. /3/ qed.

lemma leq_Sx_x_false: ∀x. S x ≤ x → False.
#x elim x #Hf /2/ qed.

lemma le_n_max_n: ∀n,m. n ≤ max n m.
#n #m normalize cut (leb n m = true ∨ leb n m = false)
// * #Htf >Htf normalize // @(leb_true_to_le …) // qed.

lemma le_le_max: ∀x, y, z. x ≤ y → x ≤ max y z.
#x #y #z #H /2/ qed.

lemma if_id_f: if false then true else false = false. // qed.
lemma if_id_t: if true then true else false = true. // qed.

lemma if_not_t: if true then false else true = false. // qed.
lemma if_not_f: if false then false else true = true. // qed.
lemma if_then_false_else_false: ∀b. if b then false else false = false. #b cases b // qed.
lemma if_then_true_else_false: ∀b. if b then true else false = b. #b cases b // qed.
lemma if_monotone: ∀P.∀b.∀(A:P). if b then A else A = A.
#P #b cases b normalize // qed.

lemma max_fact: ∀ x, y, z. max (max x z) (max y z) = max (max x y) z.
#x #y #z normalize cut (leb x z = true ∨ leb x z = false) // * #Hxz
>Hxz normalize
[ cut (leb y z = true ∨ leb y z = false) // * #Hyz >Hyz normalize
  [ cut (leb x y = true ∨ leb x y = false) // * #Hxy >Hxy normalize
    [ >Hyz normalize >if_monotone //
    | >if_monotone >Hxz normalize //
    ]
  | lapply (leb_false_to_not_le … Hyz) #Hyz'
    lapply (not_le_to_lt … Hyz') -Hyz' #Hyz'
    lapply (lt_to_le … Hyz') -Hyz' #Hyz'
    lapply (le_to_leb_true … Hyz') -Hyz' #Hyz' >Hyz' normalize
    cut (leb x y = true)
    [ lapply (leb_true_to_le … Hxz)
      lapply (leb_true_to_le … Hyz')
      -Hxz -Hyz' #Hzy #Hxz lapply (transitive_le … Hxz Hzy ) #Hxy
      @(le_to_leb_true …) @Hxy
    | #Hxy >Hxy normalize >Hyz normalize //
    ]
  ]
| cut (leb y z = true ∨ leb y z = false) // * #Hyz >Hyz normalize
  [ cut (leb y x=true)
    [ lapply (leb_false_to_not_le … Hxz) #Hxz'
      lapply (not_le_to_lt … Hxz') -Hxz' #Hxz'
      lapply (lt_to_le … Hxz') -Hxz' #Hxz'
      lapply (le_to_leb_true … Hxz') -Hxz' #Hxz' >Hxz'
      lapply (leb_true_to_le … Hyz)
      lapply (leb_true_to_le … Hxz')
      -Hyz -Hxz' #Hyz #Hxz' lapply (transitive_le … Hxz' Hyz) #Hyx
      @(le_to_leb_true …) @Hyx
    | #Hyx cut (leb x y = false)
      [ lapply (leb_true_to_le … Hyx) #Hyx'
        lapply (leb_true_to_le … Hyz) #Hyz'
        lapply (leb_false_to_not_le … Hxz) #Hxz'
        lapply (not_le_to_lt … Hxz') -Hxz' #Hxz'
        cut (y < x)
        [ @(le_to_lt_to_lt …Hyz' Hxz')
        | -Hyx #Hyx lapply (lt_to_not_le …Hyx) #Hxy
          @(not_le_to_leb_false … Hxy)
        ]
      | #Hxy >Hxy normalize >Hxz //
      ]
    ]
  | cut (leb x y = true ∨ leb x y = false) // * #Hxy
   >Hxy normalize
   [ >Hyz normalize //
   | >Hxz normalize //
   ]
  ]
]
qed.

lemma plus_tree: ∀w, x, y, z. plus (plus w x) (plus y z) = plus (plus w y) (plus x z).
#w #x #y #z /2/ qed.

lemma gtb_O: ∀x. gtb x O = false → x=0.
#x cases x normalize // #nx #abs destruct qed.

lemma times_O: ∀x. x*O=O.
#x // qed.

lemma gtb_O_true: ∀x. gtb x O=true → ∃y. x =S y.
#x cases x
[ normalize #H destruct
| #m normalize #_ @(ex_intro …)
  [ @m | //]
]
qed.


lemma neqb_refl: ∀x. neqb x x = true.
#x elim x // qed.

lemma gtb_O_plus_to_or: ∀n,m. gtb (plus n m) O = true →
 (gtb n O) = true ∨ (gtb m O) = true.

#n #m cases n cases m /2/ qed.

lemma lt_to_le_S: ∀n, m. n < m → S n ≤ m.
#n cases n // qed.

lemma max_bound: ∀ n, m, x. max n m ≤ x → n ≤ x ∧ m ≤ x.
#n #m cases n cases m #x normalize
[ #H % //
| #m' #H % //
| #n' #H % //
| #n' #m' cut (leb n' x = true ∨ leb n' x = false) // * #Htf >Htf normalize
  [ #H % // lapply (leb_true_to_le … Htf) #H1 cut (x < m') [/2/] #H2
    lapply (le_to_lt_to_lt … H1 H2) //
  | #H % // lapply (leb_false_to_not_le … Htf) #Hnle
    lapply (not_le_to_lt … Hnle) #H1 -Hnle -Htf
    normalize in H1;
    change with (n' < m') in H;
    lapply (lt_to_le … (le_to_lt_to_lt … H1 H)) //
  ]
] qed.

lemma max_swap2: ∀a, b, c. max (max a b) c = max (max a c) b.
#a #b #c >(max_comm a b) >max_comm  >max_swap >max_comm
 >(max_comm a c) // qed.

lemma max_hop: ∀a,b,c,d. max (max a b) (max c d) = max (max a c) (max b d).
#a #b #c #d normalize
cut (leb a b = true ∨ leb a b = false) // * #Hab >Hab normalize
[ cut (leb c d = true ∨ leb c d = false) // * #Hcd >Hcd normalize
  [ cut (leb b c = true ∨ leb b c = false) // * #Hbc
    [ cut (leb a c = true ∧ leb b d = true)
      [ >(le_to_leb_true …
        (transitive_le … (leb_true_to_le … Hab) (leb_true_to_le … Hbc)))
        >(le_to_leb_true …
        (transitive_le … (leb_true_to_le … Hbc) (leb_true_to_le … Hcd))) /2/
      | * #Hac #Hbd >Hac >Hbd normalize >Hcd //
      ]
    | cut (leb b d = true ∨ leb b d = false) // * #Hbd >Hbd normalize
      [ cut (leb a c = true ∨ leb a c = false) // * #Hac >Hac normalize
        [ >Hcd normalize //
        | >(le_to_leb_true …
        (transitive_le … (leb_true_to_le … Hab) (leb_true_to_le … Hbd))) //
        ]
      | cut (leb a c = true ∨ leb a c = false) // * #Hac >Hac normalize
        [ >(le_to_leb_true … (lt_to_le …
           (not_le_to_lt …(leb_false_to_not_le … Hbc)))) //
        | >Hab //
        ]
      ]
    ]
  | cut (leb b d = true ∨ leb b d = false) // * #Hbd >Hbd normalize
    [ cut (leb a c=true ∧ leb b c = true)
      [ > (le_to_leb_true … (transitive_le …
                (transitive_le … (leb_true_to_le … Hab) (leb_true_to_le … Hbd))
                (lt_to_le … (not_le_to_lt … (leb_false_to_not_le … Hcd)))))
        > (le_to_leb_true … (transitive_le …
                (leb_true_to_le … Hbd)
                (lt_to_le … (not_le_to_lt … (leb_false_to_not_le … Hcd))))) /2/
      | * #Hac #Hbc >Hac >Hbc normalize >Hcd normalize //
      ]
    | cut (leb a c = true ∨ leb a c = false) // * #Hac >Hac
      [ normalize change with (max ? ? = max ? ?) in ⊢ %; @max_comm
      | normalize >Hab normalize
        >(not_le_to_leb_false … (lt_to_not_le … (lt_to_le_to_lt …
                (not_le_to_lt … (leb_false_to_not_le … Hac))
                (leb_true_to_le … Hab)))) //
      ]
    ]
  ]
| cut (leb c d = true ∨ leb c d = false) // * #Hcd >Hcd normalize
  [ cut (leb a c = true ∨ leb a c = false) // * #Hac >Hac normalize
    [ >(le_to_leb_true … (transitive_le … (leb_true_to_le … Hac)
                                            (leb_true_to_le … Hcd)))
      > (le_to_leb_true …
              (transitive_le … (lt_to_le … (not_le_to_lt … (leb_false_to_not_le … Hab)))
              (transitive_le … (leb_true_to_le … Hac)
                                            (leb_true_to_le … Hcd))
              ))
      normalize >Hcd normalize //
    | cut (leb b d = true ∨ leb b d = false) // * #Hbd >Hbd normalize //
      >Hab normalize
      >(not_le_to_leb_false …
       (lt_to_not_le …
       (le_to_lt_to_lt …
       (lt_to_le … (not_le_to_lt … (leb_false_to_not_le … Hbd)))
       (not_le_to_lt … (leb_false_to_not_le … Hab))))) //
    ]
  | cut (leb a c = true ∨ leb a c = false) // * #Hac >Hac normalize
    [ cases (leb b d) normalize
      [ >Hcd //
      | > (not_le_to_leb_false …
               (lt_to_not_le … (lt_to_le_to_lt …
               (not_le_to_lt … (leb_false_to_not_le … Hab))
               (leb_true_to_le … Hac)))) //
      ]
    | cases (leb b d) normalize
      [ > (not_le_to_leb_false …
               (lt_to_not_le …
               (le_to_lt_to_lt …
               (lt_to_le … (not_le_to_lt … (leb_false_to_not_le … Hcd)))
               (not_le_to_lt … (leb_false_to_not_le … Hac))))) //
      | >Hab //
      ]
    ]
  ]
] qed.

lemma le_Sn_n: ∀n. S n ≤ n → False.
#n elim n /2/ qed.

lemma le_to_neqb_to_lt: ∀n,m. neqb n m = false → n ≤ m → n < m.
#n #m #H @not_eq_to_le_to_lt
lapply H
lapply (neqb_iff_eq n m) * #_ /2/
qed.

lemma max_add: ∀n, m, x. n ≤ m → n ≤ max m x.
#n #m #x #H normalize
cut (leb m x = true ∨ leb m x = false) // * #Htf >Htf normalize //
lapply (leb_true_to_le … Htf) #HH @(transitive_le … HH) // qed.
