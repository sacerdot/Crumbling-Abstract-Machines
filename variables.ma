include "crumbles.ma".
include "basics/types.ma".
include "libnat.ma".
include "utils.ma".

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

let rec inb x c on c ≝
 match c with
 [ CCrumble b e ⇒ (inb_b x b) ∨ (inb_e x e) ]

and inb_b x b on b ≝
 match b with
 [ CValue v ⇒ inb_v x v
 | AppValue v w ⇒ (inb_v x v) ∨ (inb_v x w)
 ]

and inb_e x e on e ≝
 match e with
 [ Epsilon ⇒ false
 | Snoc e s ⇒ (inb_e x e) ∨ (inb_s x s)
 ]

and inb_v x v on v ≝
 match v with
 [ var y ⇒ veqb x y
 | lambda y c ⇒  (veqb x y) ∨ (inb x c)
 ]

and inb_s x s on s ≝
 match s with
 [ subst y b ⇒ veqb x y ∨ (inb_b x b)]
 .

let rec inb_t x t on t ≝
 match t with
 [ val_to_term v ⇒ inb_tv x v
 | appl t1 t2 ⇒ (inb_t x t1) ∨ (inb_t x t2)
 ]

and inb_tv x v on v ≝
 match v with
 [ pvar y ⇒ veqb x y
 | abstr y t ⇒ (veqb x y) ∨ (inb_t x t)
 ]
.

definition inb_ec ≝ λx, ec.
 match ec with
 [ envc e y ⇒ veqb x y ∨ inb_e x e ].


definition inb_cc ≝ λx, C.
 match C with
 [ hole ⇒ false
 | crc b ec ⇒ inb_b x b ∨ inb_ec x ec ].


let rec domb x c on c ≝
 match c with
 [ CCrumble b e ⇒ domb_e x e ]

and domb_e x e on e ≝
 match e with
 [ Epsilon ⇒ false
 | Snoc e s ⇒ match s with [ subst y b ⇒ (veqb x y) ∨ (domb_e x e)]
 ].

let rec domb_ec x ec on ec ≝
 match ec with
 [ envc e y ⇒ domb_e x e ∨ veqb x y ].

let rec domb_cc x cc on cc ≝
 match cc with
 [ hole ⇒ false
 | crc b ec ⇒ domb_ec x ec
 ]
 .

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

let rec free_occ x c on c ≝
 match c with
  [ CCrumble b e ⇒ match domb_e x e with
   [ true ⇒ O
   | false ⇒ free_occ_b x b
   ] + free_occ_e x e
  ]

and free_occ_b x b on b ≝
 match b with
  [ CValue v ⇒ free_occ_val x v
  | AppValue v w ⇒ free_occ_val x v +free_occ_val x w
  ]

and free_occ_val x v on v ≝
 match v with
  [ var y ⇒ match veqb x y with [ true ⇒ 1 | false ⇒ O ]
  | lambda y c ⇒ match veqb x y with [ true ⇒ O | false ⇒ free_occ x c ]
  ]

and free_occ_e x e on e ≝
 match e with
  [ Epsilon ⇒ O
  | Snoc e s ⇒ match veqb x (match s with [subst y b ⇒ y]) with
    [ true ⇒ O
    | false ⇒ free_occ_e x e
    ] + free_occ_s x s
  ]
and free_occ_s x s on s ≝
 match s with
 [ subst y b ⇒ free_occ_b x b ].


lemma dom_push: ∀x.∀e.∀s. domb_e x (push e s) =domb_e x (Snoc e s).
#x @Environment_simple_ind2

[ * #y #b normalize //
| #e' * #y' #b' #H * #y #b normalize >(H (subst y b))
  cut (veqb x y'=true ∨ veqb x y'=false) // * #Htf
  >Htf normalize
  [ >if_monotone //
  | //
  ]
] qed.

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
 | Snoc e s ⇒ match s with [subst y b ⇒ ((fvb_e x e) ∧ (¬ veqb x y)) ∨ fvb_b x b]
 ]

and fvb_v x v on v ≝
 match v with
 [ var y ⇒ veqb x y
 | lambda y c ⇒ (¬(veqb y x) ∧ fvb x c)
 ]
 .

definition fvb_ec ≝ λx.λec.
 match ec with
 [ envc e y ⇒ match veqb x y with
   [ true ⇒ false
   | false ⇒ fvb_e x e
   ]
 ]
.

definition fvb_cc ≝ λx.λC.
 match C with
 [ hole ⇒ false
 | crc b ec ⇒ (fvb_b x b ∧ (¬domb_ec x ec)) ∨ (fvb_ec x ec)
 ]
.
let rec fvb_s x s on s ≝
 match s with
 [subst y b ⇒ fvb_b x b]
 .

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


lemma free_occ_to_fv_crumble:
 (∀c.∀x. free_occ x c = 0 ↔ fvb x c = false) ∧
  (∀b.∀x. free_occ_b x b = 0  ↔ fvb_b x b = false) ∧
   (∀e.∀x. free_occ_e x e = 0 ↔ fvb_e x e = false) ∧
    (∀v.∀x. free_occ_val x v = 0 ↔ fvb_v x v = false) ∧
     (∀s.∀x. free_occ_s x s = 0 ↔ fvb_s x s = false).

@Crumble_mutual_ind

[ #b #e #Hb #He #x %
  [ normalize cases domb_e normalize
    [ #H lapply (He x) * -He #He #_ >(He H) >if_monotone >if_f @refl
    | #H cut (free_occ_b x b = 0 ∧ free_occ_e x e = 0)
      [ % lapply H cases free_occ_b // #n normalize #H destruct
      | * -H #H1 #H2 lapply (Hb x) lapply (He x) * -He #He #_ * -Hb #Hb #_
        >He // >Hb //
      ]
    ]
  | normalize cases domb_e normalize
    [ >if_monotone >if_f #H lapply (He x) * #_ -He #He @He //
    | >if_then_true_else_false lapply (Hb x) lapply (He x) * -He -Hb
      #_ #He * #_ #Hb lapply He lapply Hb cases fvb_b cases fvb_e normalize
      [ 1,2,3: #_ #_ #abs destruct ] #Hb #He >Hb // >He //
    ]
  ]
| #v #H #x normalize @H
| #v #w #Hv #Hw #x normalize %
  [ #H cut (free_occ_val x v = 0 ∧ free_occ_val x w = 0)
    [ % lapply H cases free_occ_val cases free_occ_val // #n #m
      normalize #abs destruct
    ]
    * #Hv' #Hw' lapply (Hv x) * -Hv #Hv #_ lapply (Hw x) * -Hw #Hw #_
    >Hv // >Hw //
  | #H lapply (orb_false … H) * #Hv' #Hw' lapply (Hv x) * #_ #Hv' >Hv' //
    lapply (Hw x) * #_ #Hw' >Hw' //
  ]
| #y #x % normalize cases veqb normalize [1,3: #abs destruct ] //
| #y #c #H #x %
  [ normalize >veqb_comm cases veqb normalize // lapply (H x) * -H #H #_ @H
  | normalize >veqb_comm cases veqb normalize // lapply (H x) * -H #_ #H @H
  ]
| #c normalize % //
| #e * #y #b #He #Hs #x %
  [ normalize lapply (Hs x) normalize * -Hs #Hs #_
    cases veqb normalize
    [ >if_monotone >if_f @Hs
    | #H cut (free_occ_e x e=0 ∧ free_occ_b x b=O)
      [ % lapply H cases free_occ_e cases free_occ_b //
        #n #m normalize #abs destruct
      ]
      * #He' #Hb' >Hs // lapply (He x) * -He' #He' #_ >He' //
    ]
  | normalize lapply (Hs x) normalize * -Hs #_ #Hs
     cases veqb normalize
    [ >if_monotone >if_f @Hs
    | >if_then_true_else_false #Hor lapply (orb_false … Hor) * #He' #Hb'
      >Hs // lapply (He x) * #_ -He #He >He //
    ]
  ]
| #y #b #H #x %
  [ normalize lapply (H x) * #H' #_ @H'
  | normalize lapply (H x) * #_ #H' @H'
  ]
] qed.

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
 | Snoc e s ⇒ max (fresh_var_e e) (fresh_var_s s)
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

definition fresh_var_ec ≝ λec.
 match ec with
 [ envc e y ⇒ match y with [ variable ny ⇒ max (S ny) (fresh_var_e e) ]].

definition fresh_var_cc ≝ λC.
 match C with
 [ hole ⇒ O
 | crc b ec ⇒ max (fresh_var_b b) (fresh_var_ec ec)
 ].

lemma fvb_t_distr: ∀x,t,u. fvb_t x (appl t u)=(fvb_t x t ∨ fvb_t x u).
#x #t #u normalize cases free_occ_t cases free_occ_t normalize // qed.

lemma dom_to_in: ∀e, x. domb_e x e =true → inb_e x e =true.
@Environment_simple_ind2
[ #x normalize //
| #e * * #y #b normalize #HI * #x lapply (HI νx)
  cases veqb
  [ normalize >if_monotone //
  | >if_f >if_f #HI' #H >(HI' H) //
  ]
] qed.

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

lemma fresh_var_cons_bes: ∀b,e,s. fresh_var 〈b, e〉≤ fresh_var 〈b, Snoc e s〉.

#b @Environment_simple_ind2
[ * * #y #b
  change with (max ? O) in match (fresh_var ?); >max_O
  change with (max ? ?) in match (fresh_var ?);
  @le_n_max_n
| #e #s #H #s'
  change with (max ? ?) in match (fresh_var ?);
  change with (max ? ?) in match (fresh_var_e ?);
  change with (max ? ?) in match (fresh_var ?);
  change with (max ? ?) in match (fresh_var_e (Snoc (Snoc ? ?) ?));
  change with (max ? ?) in match (fresh_var_e (Snoc ? ?));
  /2/
] qed.

 definition fresh_var_t  ≝  λt: pTerm. pi1 nat ? (fresh_var_t_Sig t).
 definition fresh_var_tv  ≝  λv: pValue. pi1 nat ? (fresh_var_tv_Sig v).

 lemma fresh_var_val_to_term: ∀v. fresh_var_tv v = fresh_var_t (val_to_term v).
 #v normalize // qed.

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

 lemma domb_concat_distr:
 ∀x, f, e. domb_e x (concat e f) = (domb_e x e ∨ domb_e x f).
#x #f
@(Environment_simple_ind2 … f)
[ normalize #e  >if_then_true_else_false //
| #f' #s' #H #e lapply (H e) cases e normalize
  [ >H normalize #_ //
  | #e' #t' >H normalize cases s' #y #b cases t' #h #g normalize
    #_
    cut (veqb x h = true ∨ veqb x h = false) // *
    #Htf
    [ lapply (veqb_true_to_eq x h) * #Heq #_
      lapply (Heq Htf) -Heq #Heq destruct >Htf normalize
      >if_monotone //
    | >Htf normalize cut (veqb x y = true ∨ veqb x y = false) // *
      #Htf'
      [ lapply (veqb_true_to_eq x y) * #Heq #_
        lapply (Heq Htf') -Heq #Heq destruct
        >Htf' >if_t >if_monotone //
      | >Htf' normalize //
      ]
    ]
  ]
]
qed.

lemma fv_concat: ∀f, e, x. fvb_e x (concat e f) = ((fvb_e x e ∧ ¬ domb_e x f) ∨ fvb_e x f).
@Environment_simple_ind2
[ #e #x >concat_e_epsilon normalize
  >if_then_true_else_false >if_then_true_else_false //
| #f * #y #b #HI #e #x
  whd in match (concat ? (Snoc ? ?));
  whd in match (fvb_e ? (Snoc ? ?));
  whd in match (fvb_e ? (Snoc ? ?));
  whd in match (domb_e ? (Snoc ? ?));
  >HI
  cases (fvb_b x b)
  [ >if_monotone >if_monotone normalize >if_monotone //
  | >if_then_true_else_false >if_then_true_else_false
    cases veqb
    [ normalize >if_monotone >if_monotone >if_monotone >if_f //
    | normalize >if_then_true_else_false >if_then_true_else_false
      //
    ]
  ]
] qed.

 lemma veqb_fv: ∀x,z.∀t. veqb x z =true →  fvb_t x t = fvb_t z t.
 #x #z #t #h lapply (veqb_true_to_eq x z) normalize #H @(And_ind … H) -H
 #H' #H'' lapply (H' h) #Heq destruct //. qed.

 lemma free_occ_to_fv:
  ∀x. (∀t. free_occ_t x t = 0 ↔ fvb_t x t =false) ∧
   ∀v. free_occ_v x v =0 ↔ fvb_tv x v = false.

 #x @pValueTerm_ind
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

lemma fv_to_in_term:
 (∀t. ∀x. fvb_t x t = true → inb_t x t =true) ∧
  (∀v. ∀x. fvb_tv x v =true → inb_tv x v = true).

@pValueTerm_ind
[ #v #HI #x lapply (HI x) -HI normalize #HI #H @(HI H)
| #t1 #t2 #H1 #H2 #x lapply (H2 x) lapply (H1 x) -H1 -H2 normalize #H1 #H2 #H
  cut (gtb (free_occ_t x t1) O=true ∨ gtb (free_occ_t x t2) O=true)
  [ @(gtb_O_plus_to_or …) assumption
  | * -H #H
    [ >(H1 H) >if_t //
    | >(H2 H) >if_monotone //
    ]
  ]
| #x #t normalize cases (veqb t x) normalize //
| #t #y #H #x lapply (H x) -H normalize #H cases (veqb x y) normalize
  [ #abs destruct
  | #H1 @(H H1)
  ]
] qed.

lemma fresh_var_distr_crumble:
 (∀c.∀n. fresh_var c ≤ n →
   match c with [CCrumble b e ⇒ fresh_var_b b ≤ n ∧ fresh_var_e e ≤ n]) ∧
  (∀b.∀n. fresh_var_b b ≤ n →
   match b with
    [ CValue v ⇒ fresh_var_v v ≤ n
    | AppValue v w ⇒ fresh_var_v v ≤ n ∧ fresh_var_v w ≤ n
    ]) ∧
   (∀e.∀n. fresh_var_e e ≤ n →
     match e with
      [ Epsilon ⇒ True
      | Snoc e s ⇒ fresh_var_e e ≤ n ∧ fresh_var_s s ≤ n
      ]) ∧
    (∀v.∀n. fresh_var_v v ≤ n →
       match v with
       [ var x ⇒ match x with [ variable x ⇒ S x ≤ n]
       | lambda x c ⇒ match x with [ variable x ⇒ S x ≤ n] ∧ fresh_var c ≤ n
       ]) ∧
     (∀s.∀n. fresh_var_s s ≤ n →
       match s with
         [ subst y b ⇒ match y with [variable x ⇒ S x ≤n ] ∧ fresh_var_b b ≤ n]).

@Crumble_mutual_ind

[ 1,3,7: #b #e #Hb #He #n #H normalize % change with (max ? ?≤n) in H;
  [ 1,3,5: @(le_maxl … H) | 2,4,6: @(le_maxr … H)]
| 2,6: //
| * #y #n #H normalize normalize in H; //
| 5,8: * #x #c #Hc #n normalize #H % change with (max (S x) ?≤n) in H;
  [ 1,3: @(le_maxl … H) | 2,4: @(le_maxr … H)]
] qed.

lemma fv_to_in_crumble:
 (∀c.∀x. fvb x c = true → inb x c = true) ∧
  (∀b.∀x. fvb_b x b = true → inb_b x b = true) ∧
   (∀e.∀x. fvb_e x e = true → inb_e x e = true) ∧
    (∀v.∀x. fvb_v x v = true → inb_v x v = true) ∧
     (∀s.∀x. fvb_s x s = true → inb_s x s = true ).

@Crumble_mutual_ind
[ #b #e #Hb #He #x lapply (Hb x) lapply (He x) -Hb -He #He #Hb normalize
  cut (fvb_b x b=true ∨ fvb_b x b=false) // *
  #Htf >Htf normalize
  [ >(Hb Htf) normalize #_ //
  |#H >H >(He H) >if_monotone //
  ]
| #v #H #x lapply (H x) -H normalize  #H #H1 @(H H1)
| #v #w #H1 #H2 #x lapply (H2 x) lapply (H1 x) -H1 -H2 normalize
  cases (fvb_v x v) normalize
  [ #H1 #H2 #H >H1 //
  | cases (fvb_v x w) normalize
    [ #H1 #H2 #H >H2 [ >if_monotone ] //
    | #_ #_ #abs destruct
    ]
  ]
| #y #x normalize #H @H
| #y #c #H #x lapply (H x) normalize >veqb_comm cases (veqb x y) normalize
  [ #_ #abs destruct
  | #HI #H @(HI H)
  ]
| #x normalize #abs destruct
| #e #s #He #Hs #x
 lapply (Hs x) lapply (He x) cases s * #y #b normalize
  cases (veqb x (νy)) normalize //  #He' #Hs'
  >if_then_true_else_false
  change with (orb ? ?) in match (if ? then true else ?); #Hor
  change with (orb ? ?) in match (if ? then true else ?);
  cut (fvb_e x e = true ∨ fvb_b x b = true)
  [ lapply Hor cases (fvb_e x e) cases (fvb_b x b) // #_ /2/
  | *
    [ #H >(He' H) //
    | #H >(Hs' H) /2/
    ]
  ]

| #y #b #HI #x lapply (HI x) normalize
  cut (veqb x y=true ∨ veqb x y=false) // * #Htf >Htf normalize //
  cases (fvb_b x b) #HI'
  [ @HI'
  | #abs destruct
  ]
] qed.

lemma fresh_var_in:
 (∀t. ∀x. (inb_t (νx) t = true) → x < fresh_var_t t) ∧
  (∀v:pValue. ∀x. (inb_tv (νx) v = true) → x < fresh_var_tv v).

@pValueTerm_ind
[#v #H #x lapply (H x) normalize #H assumption
| #t1 #t2 #H1 #H2 #x lapply (H1 x) lapply (H2 x)
  normalize
  change with (fresh_var_t t1) in match
   (pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t1→S x0≤n) (fresh_var_t_Sig t1));
  change with (fresh_var_t t2) in match
   (pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t2→S x0≤n) (fresh_var_t_Sig t2));
  -H1 -H2 #H2 #H1
  change with (orb ? ?) in match (if ? then ? else ?);
  change with (max ? ?) in match (if (leb ? ?) then ? else ? ); #H
  lapply (orb_to_prop … H) * #Hor
  [ lapply (H1 Hor) @le_le_max
  | lapply (H2 Hor) >max_comm @le_le_max
  ]
| * #y #x normalize cut (neqb x y = true ∨ neqb x y = false)
  // * #Htf >Htf normalize
  [ lapply (neqb_iff_eq x y) * #Heq #_
    lapply (Heq Htf) -Heq #Heq destruct
    #_ //
  | #abs destruct
  ]
| #t * #y #H #x lapply (H x) #H' normalize
  change with (fresh_var_t t) in match (pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t→S x0≤n) (fresh_var_t_Sig t));
  change with (leb (S ?) ?) in match (match ? in nat with [_ ⇒ ?]);
  change with (max ? ?) in match (if leb ? ? then ? else ?);
  cut (neqb x y = true ∨ neqb x y = false) // * #Htf
  [ lapply (neqb_iff_eq x y) * #Heq #_
    lapply (Heq Htf) -Heq #Heq destruct >Htf >if_t
    #_ @le_n_max_n
  | >Htf >if_f #HH >max_comm @le_le_max @(lt_to_le_S … (H' HH))
  ]
] qed.

(*bisognerebbe dare fv_fresh come corollario del precedente*)

lemma fv_fresh:
 (∀t. ∀x. (fvb_t (νx) t = true) → x < fresh_var_t t) ∧
  (∀v:pValue. ∀x. (fvb_tv (νx) v = true) → x < fresh_var_tv v).

%
[ #t #x #H cut (inb_t (νx) t = true)
  [ lapply fv_to_in_term * #Hfv_to_in_term #_
    >(Hfv_to_in_term t (νx) H) //
  | lapply fresh_var_in * #Hfresh_var_in #_ @Hfresh_var_in
  ]
| #v #x #H cut (inb_tv (νx) v = true)
  [ lapply fv_to_in_term * #_ #Hfv_to_in_term
    >(Hfv_to_in_term v (νx) H) //
  | lapply fresh_var_in * #_ #Hfresh_var_in @Hfresh_var_in
  ]
] qed.

lemma fresh_var_sup:
 (∀t. inb_t (ν(fresh_var_t t - 1)) t = true) ∧
  (∀v. inb_tv (ν(fresh_var_tv v - 1)) v = true).

@pValueTerm_ind
[ #v normalize #H @H
| #t1 #t2 normalize
  change with (fresh_var_t t1)
   in match (pi1 ℕ (λn:ℕ.∀x:ℕ.1≤free_occ_t (νx) t1→S x≤n) (fresh_var_t_Sig t1));
  change with (fresh_var_t t2)
   in match (pi1 ℕ (λn:ℕ.∀x:ℕ.1≤free_occ_t (νx) t2→S x≤n) (fresh_var_t_Sig t2));
  change with (max ? ?)
   in match (if leb ? ? then ? else ?);
  lapply (max_n_m (fresh_var_t t1) (fresh_var_t t2)) *
  [ #H >H #H1 >H1 //
  | #H >H #_ #H2 >H2 >if_monotone //
  ]
| #x cases x #nx normalize //
| #t * #x normalize
  change with (fresh_var_t t)
   in match (pi1 ℕ (λn:ℕ.∀x:ℕ.1≤free_occ_t (νx) t→S x≤n) (fresh_var_t_Sig t));
  change with (leb (S ?) ?) in match (match ? in nat with [_ ⇒ ? ]);
  change with (max ? ?)
   in match (if leb ? ? then ? else ?);
  lapply (max_n_m (S x) (fresh_var_t t)) * #H >H
  [ #_ normalize cut (x-0=x)// #Heq >Heq >neqb_refl normalize //
  | #H1 >H1 >if_monotone //
  ]
] qed.

lemma fresh_var_push: ∀e, s. (fresh_var_e (Snoc e s))=fresh_var_e (push e s).

#e @(Environment_simple_ind2 … e)
[ #s normalize //
| #e' #s' #HI #s lapply (HI s) normalize #HI <HI
  change with (max ? ?) in match (if leb (fresh_var_e e') (fresh_var_s s') 
        then fresh_var_s s' 
        else fresh_var_e e' );
  change with (max ? ?) in match (if leb (fresh_var_e e') (fresh_var_s s) 
         then fresh_var_s s 
         else fresh_var_e e');
  change with ((max ? ?)=(max ? ?)) in  ⊢ %; /2/
] qed.

lemma fresh_var_concat:
 ∀f, e. fresh_var_e (concat e f) = max (fresh_var_e e ) (fresh_var_e f).

 #f @(Environment_simple_ind2 … f)
[ normalize #e change with (max ? O) in match (if ? then ? else ?); >max_O //
| #f' #s' #H #f cases f normalize
  [ >H normalize
    change with (max ? ?) in match (if ? then ? else ?); //
  | #e #t >H normalize cases s' * #y #b cases t * #h #g normalize
    change with (leb (S ?) ?) in match (match fresh_var_b b in nat return λ_:ℕ.bool with 
                    [O⇒false|S (q:ℕ)⇒leb y q] );
    change with (leb (S ?) ?) in match (match fresh_var_b g in nat return λ_:ℕ.bool with 
                          [O⇒false|S (q:ℕ)⇒leb h q]);
    change with (max ? ?) in match (if leb (S y) (fresh_var_b b) then fresh_var_b b else S y);
    change with (max ? ?) in match (if leb (fresh_var_e f) (max (S y) (fresh_var_b b)) 
              then max (S y) (fresh_var_b b) 
              else fresh_var_e f);
    change with (max ? ? = max ? ?) in ⊢ %;
    change with (max ? ?)
        in match (if leb (fresh_var_e e)
                 (if leb (S h) (fresh_var_b g) then fresh_var_b g else S h ) 
                  then if leb (S h) (fresh_var_b g) then fresh_var_b g else S h  
                  else fresh_var_e e );
    change with (max ? ?) in match ((if leb (S h) (fresh_var_b g) then fresh_var_b g else S h ));
    change with (max ? ?)
        in match (if leb (max (fresh_var_e e) (max (S h) (fresh_var_b g))) (fresh_var_e f') 
                  then fresh_var_e f' 
                  else max (fresh_var_e e) (max (S h) (fresh_var_b g)) );
    change with (max ? ?)
      in match ((if leb (fresh_var_e f') (max (S y) (fresh_var_b b)) 
    then max (S y) (fresh_var_b b) 
    else fresh_var_e f' ));
    letin z≝ (max (S y) (fresh_var_b b))
    letin w≝ (max (S h) (fresh_var_b g))
    /2/
  ]
]
qed.

lemma fresh_var_to_in:
 (∀t.∀m. (fresh_var_t t≤m→inb_t (νm) t=false)) ∧
  (∀v.∀m. (fresh_var_tv v≤m→inb_tv (νm) v=false)).

@pValueTerm_ind
[ #v normalize #H @H
| #t1 #t2 #H1 #H2 #m normalize
  change with (fresh_var_t t1)
    in match (pi1 ? ? (fresh_var_t_Sig t1));
  change with (fresh_var_t t2)
    in match (pi1 ? ? (fresh_var_t_Sig t2));
  change with (max ? ?) in match (if ? then ? else ?);
  #H
  >(H1 … (le_maxl … H)) >(H2 … (le_maxr … H)) //
| * #x #m normalize
  cut (neqb m x = true ∨ neqb m x = false) // * #Htf >Htf
  [ lapply (neqb_iff_eq m x) * #Heq #_ lapply (Heq Htf) -Heq
    #Heq destruct #abs @False_ind /2/
  | #_ //
  ]
| #t * #x #HI #m normalize
  change with (fresh_var_t t)
    in match (pi1 ? ? (fresh_var_t_Sig t));
  change with (max (S x) (fresh_var_t t))
    in match (if ? then ?  else ?);
  #H >(HI … (le_maxr … H))
  >if_then_true_else_false
  cut (neqb m x = true ∨ neqb m x = false) // * #Htf
  [ lapply (neqb_iff_eq … m x) * #Heq #_ lapply (Heq Htf)
    -Heq #Heq destruct @False_ind
    lapply (le_maxl … H) #abs /2/
  | @Htf
  ]
] qed.

lemma fresh_var_to_in_crumble:
 (∀c.∀x. fresh_var c ≤ x → inb (νx) c = false) ∧
  (∀b.∀x. fresh_var_b b ≤ x → inb_b (νx) b = false) ∧
   (∀e.∀x. fresh_var_e e ≤ x → inb_e (νx) e = false) ∧
    (∀v.∀x. fresh_var_v v ≤ x → inb_v (νx) v = false) ∧
     (∀s.∀x. fresh_var_s s ≤ x → inb_s (νx) s = false ).

@Crumble_mutual_ind
[ #b #e #Hb #He #x
 change with (max (fresh_var_b ?) (fresh_var_e ?)) in match  (fresh_var ?);
 #Hm normalize
 >(Hb … (le_maxl … Hm)) >(He … (le_maxr … Hm )) //
| #v #Hv #x #H normalize in H; @(Hv … H)
| #v #w #Hv #Hw #x
  change with (max (fresh_var_v ?) (fresh_var_v ?)) in match  (fresh_var_b ?);
  #Hm normalize
  >(Hv … (le_maxl … Hm)) >(Hw … (le_maxr … Hm )) //
| * #y #x normalize
  cut (neqb x y = true ∨ neqb x y = false) // * #Htf
  [ lapply (neqb_iff_eq x y) * #Heq #_ lapply (Heq Htf) -Heq #Heq destruct #abs
    @False_ind /2/
  | #_ @Htf
  ]
| * #y #c #Hc #x
  change with (max (S y) (fresh_var c)) in match (fresh_var_v ?);
  #Hm
  change with ((neqb x y) ∨ (inb (νx) c)) in match (inb_v ? ?);
  >(Hc … (le_maxr … Hm))
  cut (neqb x y = true ∨ neqb x y = false) // * #Htf
  [ lapply (neqb_iff_eq x y) * #Heq #_ lapply (Heq Htf) -Heq
    #Heq destruct @False_ind lapply (le_maxl … Hm) /2/
  | >Htf //
  ]
| #x normalize //
| #e #s #He #Hs #x
  change with (max ? ?) in match (fresh_var_e ?);
  #Hm normalize
  >(He … (le_maxl … Hm)) >(Hs … (le_maxr … Hm )) //
| * #y #b #Hb #x
  change with (max (S y) (fresh_var_b b)) in match (fresh_var_s [νy ← b]);
  #Hm
  change with ((neqb x y) ∨ (inb_b (νx) b)) in match (inb_s ? ?);
  >(Hb … (le_maxr … Hm))
  cut (neqb x y = true ∨ neqb x y = false) // * #Htf
  [ @False_ind lapply (neqb_iff_eq x y) * #Heq #_ lapply (Heq Htf) -Heq
    #Heq destruct lapply (le_maxl … Hm) /2/
  | >Htf //
  ]
] qed.

lemma fv_push: ∀x, e, y, b. fvb_e x (push e [y←b]) = (fvb_e x e ∨ (¬domb_e x e ∧ fvb_b x b)).
#x @Environment_simple_ind2
[ #y #b normalize cases fvb_b //
| #e' * * #k #p #H #y #b
  whd in match (push ? ?);
  whd in match (fvb_e x (Snoc (push ? ?) ?));
  whd in match (fvb_e x (Snoc (?) ?));
  whd in match (domb_e ? ?); >H
  cases fvb_e cases fvb_b cases fvb_b cases veqb normalize cases domb_e //
] qed.

let rec oab_occ x c on c ≝
 match c with
 [ CCrumble b e ⇒ match (domb_e x e) with [ true ⇒  (oab_occ_b x b) | false ⇒ O ] + (oab_occ_e x e false) ]

and oab_occ_b x b on b ≝
 match b with
 [ CValue v ⇒ (oab_occ_v x v)
 | AppValue v w ⇒ (oab_occ_v x v) + (oab_occ_v x w)
 ]

and oab_occ_v x v on v ≝
 match v with
 [ var y ⇒ match veqb x y with [ true ⇒ 1 | false ⇒ O]
 | lambda y c ⇒ O
 ]

and oab_occ_e x e d on e ≝
 match e with
 [ Epsilon ⇒ O
 | Snoc e s ⇒ match s with
   [ subst y b ⇒  match d with
     [ true ⇒ oab_occ_b x b
     | false ⇒ O
     ] + oab_occ_e x e (orb (veqb x y) d)
   ]
 ]
(*
and oab_occ_e x e d on e ≝
 match e with
 [ Epsilon ⇒ O
 | Snoc e s ⇒ oab_occ_s x s + match d with
   [ true  ⇒  oab_occ_e x e (veqb x match s with [ subst y b ⇒ y])
   | false ⇒ O
   ]
 ]

and oab_occ_s x s on s ≝
 match s with
 [ subst y b ⇒ oab_occ_b x b]
 *).

lemma free_occ_push: ∀e, x, s.
 free_occ_e x (push e s) =
  if (domb_e x e)
  then (free_occ_e x e)
  else (free_occ_e x e + free_occ_s x s).

@Environment_simple_ind2
[ #x * #y #b normalize >if_monotone //
| #e * #y #b #HI #x #s'
  whd in match (push ? ?);
  whd in match (free_occ_e x ?);
  whd in match (match ? in Substitution with [_⇒?]);
  >HI
  normalize cases veqb normalize // cases domb_e // >if_f >if_f /2/
] qed.

lemma free_occ_concat:
 ∀f, e, x.
  free_occ_e x (concat e f) =
   if (domb_e x f)
   then free_occ_e x f
   else free_occ_e x e + free_occ_e x f.

@Environment_simple_ind2
[ #e #x whd in match (concat ? ?);
  whd in match (domb_e ? ?); >if_f
  whd in match (free_occ_e x Epsilon); //
| #f * #y #b #H #e #x
  whd in match (concat ? ?);
  whd in match (domb_e ? ?);
  whd in match (free_occ_e ? ?);
  whd in match (free_occ_e ? (Snoc f [y ←b]));
  whd in match (match ? in Substitution with  [_⇒?]);
  whd in match (free_occ_s ? ?); >H
  cases veqb // >if_f >if_f >if_f
  cases domb_e // >if_f >if_f //
] qed.

lemma inb_push: ∀e, x, s. inb_e x (push e s) = inb_e x (Snoc e s).
@Environment_simple_ind2
[ #x #s normalize //
| #e * #y #b #HI #x #s whd in match (push (Snoc e ?) s);
  whd in match (inb_e ? ?);
  whd in match (inb_e ? (Snoc (Snoc ? ?) ?));
  >HI
  whd in match (inb_e x (Snoc e s));
  whd in match (inb_e x (Snoc e [y←b]));
  whd in match (inb_s x [y←b]);
  whd in match (inb_s x [y←b]);
  cases inb_e // >if_f >if_f
  cases veqb // >if_f
  cases inb_s normalize
  [ >if_monotone //
  | >if_then_true_else_false //
  ]
] qed.

lemma inb_concat: ∀f, e, x. inb_e x (concat e f) = (inb_e x e ∨ inb_e x f).
@Environment_simple_ind2
[ #e #s normalize >if_then_true_else_false //
| #f * #y #b #HI #e #x
  whd in match (concat ? ?);
  whd in match (inb_e ? ?);
  whd in match (inb_s ? ?);
  whd in match (inb_e ? (Snoc (?) ?));
  whd in match (inb_s ? ?);
  >HI
  cases veqb
  [ >if_t >if_monotone >if_monotone
    change with (if ? then ? else ?) in match (orb ? ?); >if_monotone // ]
  >if_f
  cases inb_e //
] qed.

let rec nua x c on c ≝
 match c with
 [ CCrumble b e ⇒ nua_e x e ∧ nua_b x b ]

and nua_b x b on b ≝
 match b with
 [ AppValue v1 v2 ⇒ nua_v x v1 ∧ nua_v x v2
 | CValue v ⇒ nua_v x v
 ]

and nua_v x v on v ≝
 match v with
 [ var x ⇒ true
 | lambda z c ⇒ match veqb z x with
   [ true ⇒ true
   | false ⇒ ¬(fvb x c)
   ]
 ]

and nua_e x e on e ≝
 match e with
 [ Epsilon ⇒ true
 | Snoc e s ⇒ nua_e x e ∧ nua_s x s
 ]

and nua_s x s on s ≝
 match s with
 [ subst y b ⇒ nua_b x b ]
.

let rec nua_t x t on t ≝
 match t with
 [ val_to_term v ⇒ nua_tv x v
 | appl u1 u2 ⇒ (nua_t x u1) ∧ (nua_t x u2)
 ]

and nua_tv x v on v ≝
 match v with
 [ pvar x ⇒ true
 | abstr z t ⇒ match veqb z x with
   [ true ⇒ true
   | false ⇒ ¬(fvb_t x t)
   ]
 ]
.

lemma fvb_to_nua_term:
 (∀t, x. fvb_t x t = false → nua_t x t = true) ∧
  (∀v, x. fvb_tv x v = false → nua_tv x v = true).
@pValueTerm_ind
[ #v #H @H
| #t1 #t2 #H1 #H2 #x normalize #H
  cut (fvb_t x t1 = false ∧ fvb_t x t2 = false)
  [ lapply H normalize cases free_occ_t cases free_occ_t
    normalize
    [ #_ % @refl
    | #n #abs destruct
    | #m #abs destruct
    | #n #m #abs destruct
    ]
  ] * #Ha #Hb >H1 // >H2 //
| * #z * #x normalize #_ //
| #t #z #HI #x normalize >veqb_comm cases veqb normalize //
  #H >H //
] qed.

lemma inb_to_nua_crumble:
 (∀c.∀x. inb x c = false → nua x c = true) ∧
  (∀b.∀x. inb_b x b = false → nua_b x b = true) ∧
   (∀e.∀x. inb_e x e = false → nua_e x e = true) ∧
    (∀v.∀x. inb_v x v = false → nua_v x v = true) ∧
     (∀s.∀x. inb_s x s = false → nua_s x s = true).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #H whd in match (nua ? ?);
  >Hb [ 2: lapply H normalize cases inb_b // normalize #abs @abs ]
  >if_then_true_else_false >He // lapply H normalize cases inb_e //
  >if_monotone #H @H
| #v #HI @HI
| #v #w #Hv #Hw #x whd in match (inb_b x (AppValue ? ?)); #H
  lapply (orb_false …H) * #Ha #Hb
  whd in match (nua_b ? ?); >Hv >Hw //
| //
| #z #c #HI #x whd in match (inb_v x ?);
  whd in match (nua_v ? ?); cases veqb [ >if_t #abs destruct ]
  >if_f #H cut (fvb x c = false) [ 2: #HH >HH // ] lapply H
  @(bool_impl_inv2 ? ? ? ?) lapply fv_to_in_crumble * * * * #Hc #_ #_ #_ #_
  @Hc
| //
| #e #s #He #Hs #x normalize #H lapply (orb_false … H) * -H #H1 #H2
  >He // >Hs //
| #y #b #HI #x normalize cases veqb [ >if_t #abs destruct ]
  >if_f @HI
] qed.

lemma nua_push: ∀e, x, s. nua_e x (push e s) = nua_e x (Snoc e s).
@Environment_simple_ind2
[ #x #s normalize //
| #e #s #HI #x #s1
  whd in match (push ? ?);
  whd in match (nua_e ? ?);
  >HI normalize cases nua_e // >if_t >if_t
  cases nua_s cases nua_s normalize //
] qed.

lemma nua_concat: ∀f, e, x. nua_e x (concat e f) = ((nua_e x e) ∧ (nua_e x f)).
@Environment_simple_ind2 [ normalize #e #x >if_then_true_else_false // ]
#f #s #HI #e #x
whd in match (concat ? ?);
whd in match (nua_e ? ?); >HI
normalize cases nua_e //
qed.
