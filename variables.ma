include "crumbles.ma".
include "basics/types.ma".
include "libnat.ma".
include "utils.ma".

let rec domb x c on c ≝
 match c with
 [ CCrumble b e ⇒ domb_e x e ]

and domb_e x e on e ≝
 match e with
 [ Epsilon ⇒ false
 | Cons e s ⇒ match s with [ subst y b ⇒ (veqb x y) ∨ (domb_e x e)]
 ].

let rec free_occ_t x t on t ≝
 match t with
 [val_to_term v ⇒ free_occ_v x v
 |appl t1 t2 ⇒ (free_occ_t x t1)+(free_occ_t x t2)
 ]

and free_occ_v x v on v ≝
 match v with
 [ pvar y ⇒ match veqb x y with [ true ⇒ 1 | false ⇒ 0]
 | abstr y t ⇒ match (veqb x y) with [ true ⇒ 0 | false ⇒ (free_occ_t x t)]
 ]
.

definition fv_t ≝ λx.λt. (free_occ_t x t)>0.
definition fv_v ≝ λx.λv. (free_occ_v x v)>0.
definition fvb_t ≝ λx.λt. gtb (free_occ_t x t) 0.
definition fvb_tv ≝ λx.λv. gtb (free_occ_v x v) 0.

let rec fvb x c on c : bool ≝
 match c with
 [ CCrumble b e ⇒ ((fvb_b x b) ∧ ¬(domb_e x e)) ∨ fvb_e x e ]

and fvb_b x b on b ≝
 match b with
 [ CValue v ⇒ fvb_v x v
 | AppValue v w ⇒ (fvb_v x v) ∨ (fvb_v x w)
 ]

and fvb_e x e on e ≝
 match e with
 [ Epsilon ⇒ false
 | Cons e s ⇒ match s with [subst y b ⇒ ((fvb_e x e) ∧ (¬ veqb x y)) ∨ fvb_b x b]
 ]

and fvb_v x v on v ≝
 match v with
 [ var y ⇒ veqb x y
 | lambda y c ⇒ (¬(veqb y x) ∧ fvb x c)
 ]
 .

let rec fvb_s x s on s ≝
 match s with
 [subst y b ⇒ (¬ veqb x y) ∨ fvb_b x b]
 .

let rec fresh_var c on c ≝
 match c with
 [ CCrumble b e ⇒  max (fresh_var_b b) (fresh_var_e e)]

and fresh_var_b b on b ≝
 match b with
 [ CValue v ⇒ fresh_var_v v
 | AppValue v w ⇒ max (fresh_var_v v) (fresh_var_v w)
 ]

and fresh_var_e e on e ≝
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒ max (fresh_var_e e) (fresh_var_s s)
 ]

and fresh_var_v v on v ≝
 match v with
 [ var y ⇒ match y with [ variable x ⇒ S x ]
 | lambda y c ⇒ match y with [ variable x ⇒ max (S x) (fresh_var c)]
 ]

and fresh_var_s s on s ≝
 match s with
 [ subst x b ⇒ match x with [ variable x ⇒ max (S x) (fresh_var_b b)] ]
 .

 let rec fresh_var_t_Sig t on t : Σn: nat. (∀x. (free_occ_t (νx) t ≥ 1) → (n > x)) ≝
  match t return λt. Σn: nat. (∀x. (free_occ_t (νx) t ≥ 1) → (n > x)) with
  [ val_to_term v ⇒ mk_Sig nat ? (pi1 nat ? (fresh_var_tv_Sig v)) ?
  | appl v w ⇒ mk_Sig nat ? (max (pi1 nat ? (fresh_var_t_Sig v)) (pi1 nat ? (fresh_var_t_Sig w))) ?
  ]

 and fresh_var_tv_Sig v on v : Σn: nat. (∀x. (free_occ_v (νx) v ≥ 1) → (n > x)) ≝
  match v return λv. Σn: nat. (∀x. (free_occ_v (νx) v ≥ 1) → (n > x)) with
  [ pvar y ⇒ match y return λy. Σn: nat. (∀x. (free_occ_v (νx) (pvar y) ≥ 1) → (n > x)) with [variable x ⇒ mk_Sig … (S x) ?]
  | abstr y t ⇒ match y return λy. Σn: nat. (∀x. (free_occ_v (νx) (abstr y t) ≥ 1) → (n > x)) with [variable x ⇒ mk_Sig … (max (S x) (pi1 nat ? (fresh_var_t_Sig t))) ?]
  ]
  .
 [ @sigma_prop_gen #z #z_def #H #x  #H1 normalize in H1; cut (free_occ_v (νx) v ≥1)
   [ /2/ assumption
   | -H1 #H1 @((H x) H1)
   ]
 | @sigma_prop_gen #z #z_def @sigma_prop_gen #z1 #z1_def #H1 #H #x #HH normalize in HH;
   lapply HH lapply (H x) cases (free_occ_t (νx) v)
   [ #_ -HH #HH lapply (H1 x) -H1 #H1 cut (z1 > x)
     /2/ -H1 #H1  normalize cut (leb z z1= true ∨ leb z z1= false) // * #Htf >Htf
     normalize /2/ lapply(leb_false_to_not_le z z1 Htf )
     -Htf #Htf lapply (not_le_to_lt z z1 Htf) #Hgt normalize in H1;
     @(lt_to_le (S x) z (le_to_lt_to_lt (S x) z1 z H1 Hgt))
   | #n #Hzx cut (z>x)[ /2/ | -Hzx #Hzx  #Hok normalize
     cut (leb z z1= true ∨ leb z z1= false) // * #Htf >Htf
     normalize[ lapply(leb_true_to_le z z1 Htf)
     normalize in Hzx; /2/ | /2/]]
   ]
 | #z  normalize cut (neqb z x=true ∨ neqb z x=false) // * #Htf >Htf normalize
   [ #_ lapply(neqb_iff_eq z x) * #Heq #_ lapply (Heq Htf) -Heq #Heq destruct //
   | #Abs @False_ind /2/
   ]
 | @sigma_prop_gen #z #z_def #H #y normalize cut (neqb y x = true ∨ neqb y x = false) // * #Htf
   >Htf normalize
   [ #Abs @False_ind /2/
   | #HH lapply ((H y) ((leq_to_geq 1 (free_occ_t (νy) t)) HH)) #Hgt
     change with (leb (S ?) ?) in match ( match z in nat return λ_:ℕ.bool with [O⇒false|S (q:ℕ)⇒leb x q]) ;
     cut (leb (S x) z=true ∨ leb (S x) z=false)  // * #Htf2 >Htf2 normalize
     normalize in Hgt; [ assumption |
     lapply(not_le_to_lt (S x) z ((leb_false_to_not_le (S x) z) Htf2))
     #Hgt2 @(lt_to_le … (le_to_lt_to_lt (S y) z (S x) Hgt Hgt2))
 ] qed.

 definition fresh_var_t  ≝  λt: pifTerm. pi1 nat ? (fresh_var_t_Sig t).
 definition fresh_var_tv  ≝  λv: pifValue. pi1 nat ? (fresh_var_tv_Sig v).

 lemma fresh_var_gt: ∀x.(∀t. (free_occ_t (νx) t ≥ 1) → (fresh_var_t t) > x) ∧
                         (∀v. (free_occ_v (νx) v ≥ 1) → (fresh_var_tv) v > x).
 #x % [ #t normalize @sigma_prop_gen #z #z_def #H /2/
 | #v normalize @sigma_prop_gen #z #z_def #H /2/].qed.

 lemma fresh_var_abstr_decr: ∀x, t. fresh_var_t t≤ fresh_var_tv (abstr x t).
 #x #t whd in match (fresh_var_tv ?); cases x #nx
 change with (« max (S nx) (pi1 nat ? (fresh_var_t_Sig t)), ?») in match (fresh_var_tv_Sig ?);
 whd in match (fresh_var_t ?); >max_comm @le_n_max_n qed.

 lemma free_occ_max: ∀x, t. free_occ_t (variable (max (fresh_var_t t) x)) t=0.
 #x #t normalize cut (leb (fresh_var_t t) x= true ∨  leb (fresh_var_t t) x= false)
 // * #Htf >Htf normalize
 [ lapply (leb_true_to_le … Htf) -Htf #Hle lapply (fresh_var_gt x) * #H1
   lapply (H1 t) -H1 #H1 #_ lapply(inverse … H1) -H1 #H1 normalize in match (¬? ≥1) in H1;
   normalize cut ((fresh_var_t t)≤x→free_occ_t (νx) t=0)
    [ lapply (not_ge_1_to_O … (H1 ((le_to_not_gt … (fresh_var_t t) x) Hle))) //
    | #H2 @(H2 Hle)
    ]
 | @sigma_prop_gen #z #z_def #Hz lapply(leb_false_to_not_le (fresh_var_t t) x Htf)
   -Htf #H1 lapply((not_le_to_lt (fresh_var_t t) x) H1) -H1 #H1
   lapply (Hz z) -Hz #Hx lapply (inverse … Hx) normalize
   cut (S z ≰ z) // #H1 #H2  @(not_ge_1_to_O … (H2 H1))
 ]
 qed.

 lemma veqb_comm: ∀x.∀y. veqb x y  = veqb y x.
 #x #y elim x #nx elim y #ny normalize //. qed.

 lemma veqb_true: ∀x. veqb x x = true.
 #x elim x #nx elim nx normalize // qed.

 lemma veqb_trans: ∀x,y,z. (veqb x y) = true → (veqb y z) = true → (veqb x z)=true.
 #x #y #z lapply ((veqb_true_to_eq x y)) #H1 lapply ((veqb_true_to_eq y z)) #H2
 #H3 #H4 normalize in H1; normalize in H2; cut (x=z)
 [ @(And_ind … H1) #H1' #H1'' -H1 @(And_ind … H2) #H2' #H2'' -H2 lapply (H1' H3) lapply (H2' H4) //
 | #H destruct -H1 -H2 -H3 -H4 elim z #nz normalize //] qed.

 lemma veqb_simm: ∀x,y. (veqb x y) = veqb y x.
 #x #y elim x #nx elim y #ny normalize /2/ qed.

 lemma veqb_fv: ∀x,z.∀t. veqb x z =true →  fvb_t x t = fvb_t z t.
 #x #z #t #h lapply (veqb_true_to_eq x z) normalize #H @(And_ind … H) -H
 #H' #H'' lapply (H' h) #Heq destruct //. qed.

 lemma free_occ_to_fv:
  ∀x. (∀t. free_occ_t x t = 0 ↔ fvb_t x t =false) ∧
   ∀v. free_occ_v x v =0 ↔ fvb_tv x v = false.

 #x @pifValueTerm_ind
 [ #v * #H1 #H2 %
  [ normalize @H1
  | normalize @H2
  ]
 | #t1 #t2 * #Ha1 #Ha2 * #Hb1 #Hb2 %
  [ normalize #H cut (free_occ_t x t1 = 0 ∧ free_occ_t x t2 = 0)[ % /2/]
  * #Hc1 #Hc2 lapply (Ha1 Hc1) lapply (Hb1 Hc2) normalize
  -Ha1 #Ha1 -Hb1 #Hb1 lapply (gtb_O … Ha1) lapply (gtb_O … Hb1)
  -Ha1 -Hb1 #Ha1 #Hb1 >Ha1 >Hb1 //
  | normalize #H @(gtb_O … H)
  ]
 | #y normalize cases (veqb) normalize % #H [ 1,2: destruct | 3,4: //]
 | #t #y * #H1 #H2 % #H
   [ normalize normalize in H; >H //
   | change with (gtb (free_occ_v x ?) O) in match (fvb_tv ? ?) in H;
     whd in match (free_occ_v ? ?) in H; normalize lapply H
     cases veqb normalize // -H #H @(gtb_O … H)
   ]
 ] qed.
