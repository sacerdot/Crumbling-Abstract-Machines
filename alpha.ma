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

include "well_named.ma".
include "basics/lists/list.ma".
include "environments.ma".

lemma alpha_lemma1: ∀z,b,e. inb z 〈b,e〉=false → (inb_e z e=false).
#z #b #e normalize cases inb_e // >if_monotone #H @H qed.

lemma alpha_lemma2: ∀z,b,e. (inb z 〈b,e〉=false) → (inb_b z b=false).
#z #b #e normalize cases inb_b // >if_t #H @H qed.

lemma alpha_lemma3: ∀z, v. inb_b z (CValue v)=false → (inb_v z v=false).
#z #v normalize #H @H qed.

lemma alpha_lemma4: ∀z, v, w. inb_b z (AppValue v w)=false → inb_v z v=false.
#z #v #w normalize cases inb_v // >if_t #H @H qed.

lemma alpha_lemma5: ∀z, v, w. inb_b z (AppValue v w)=false → inb_v z w=false.
#z #v #w normalize cases (inb_v z w) // >if_monotone #H @H qed.

lemma alpha_lemma6: ∀z, x, c. inb_v z (𝛌x.c)=false → (inb z c=false).
#z #x #c normalize cases inb // >if_monotone #H @H qed.

lemma alpha_lemma7: ∀z, e, w, b. inb_e z (Snoc e [w←b])=false → (inb_b z b=false).
#z #e #w #b normalize cases inb_b // >if_monotone >if_monotone #H @H qed.

lemma alpha_lemma8: ∀z, e, w, b. inb_e z (Snoc e [w←b])=false → (inb_e z e=false).
#z #e #w #b normalize cases inb_e // >if_t #H @H qed.

let rec ssc c y z on c: inb z c = false → Crumble ≝
 match c return λc. inb z c = false → Crumble with 
  [ CCrumble b e ⇒ λp. 〈ssb b y z ?, sse e y z ?〉
  ]

and ssb b y z on b: inb_b z b = false → Bite ≝
 match b return λg. inb_b z g = false → Bite with
 [ CValue v ⇒ λp. CValue (ssv v y z ?)
 | AppValue v w ⇒ λp. AppValue (ssv v y z ?) (ssv w y z ?)
 ]
 
and ssv v y z on v: inb_v z v = false → Value ≝ 
 match v return λv. inb_v z v = false → Value with
 [ var x ⇒ λp. match veqb x y with [true ⇒ var z | false ⇒ var x]
 | lambda x c ⇒ match veqb x y with [true ⇒ λp. lambda x c | false ⇒ λp. lambda x (ssc c y z ?)]
 ]
 
and sse e y z on e: inb_e z e = false → Environment ≝
 match e return λe. inb_e z e = false → Environment with
 [ Epsilon ⇒ λp. Epsilon
 | Snoc e s ⇒ match s return λs. inb_e z (Snoc e s) = false → Environment with
    [ subst w b ⇒ match veqb y w with
      [ true ⇒ λp. Snoc (sse e y z ?) [z←ssb b y z ?]
      |  false ⇒ λp. Snoc (sse e y z ?) [w←ssb b y z ?]
      ]
    ]
 ]
.

[ @(alpha_lemma2 … e … p)
| @(alpha_lemma1 … b … p)
| @(alpha_lemma3 … p)
| @(alpha_lemma4 … w … p)
| @(alpha_lemma5 … v … p)
| @(alpha_lemma6 … x … p)
| @(alpha_lemma8 … w b … p)
| @(alpha_lemma7 … e w … p)
| @(alpha_lemma8 … w b … p)
| @(alpha_lemma7 … e w … p)
] qed.


let rec sss s (y:Variable) (z:Variable) on s: inb_s z s = false → Substitution ≝
 match s return λs. inb_s z s = false → Substitution with
 [ subst x b ⇒ λp. subst x (ssb b y z ?)]
 .
lapply p normalize cases inb_b // >if_monotone #H @H qed.

(*
let rec ssc c y z on c ≝
 match c with (*va aggiunto il controllo sul dominio: se y è legata dal dominio di e,
                non va sostituita; allo stesso modo, se z è nel dominio di e non va sostituita,
                ma nella funzione alpha ciò non avviene.*)
  [ CCrumble b e ⇒ 〈 ssb b y z, sse e y z〉 ]

and ssb b y z on b ≝
 match b with
 [ CValue v ⇒ CValue (ssv v y z)
 | AppValue v w ⇒ AppValue (ssv v y z) (ssv w y z)
 ]
 
and ssv v y z on v ≝ 
 match v with
 [ var x ⇒ match veqb x y with [true ⇒ var z | false ⇒ var x]
 | lambda x c ⇒ match veqb x y with [true ⇒ lambda x c | false ⇒ lambda x (ssc c y z)]
 ]
 
and sse e y z on e ≝
 match e with
 [ Epsilon ⇒ Epsilon
 | Snoc e s ⇒ match s with [ subst w b ⇒ match veqb y w with
                                          [ true ⇒ Snoc e [w←ssb b y z]
                                          |  false ⇒ Snoc (sse e y z) [w←ssb b y z]
                                          ]
                           ]
 ]
.
 
let rec sss s (y:Variable) (z:Variable) on s ≝
 match s with
 [ subst x b ⇒ subst x (ssb b y z)]
 .
*)

lemma ssc_step: ∀b, e, y, z,H. ssc 〈b, e〉 y z H= 〈ssb b y z ?,sse e y z ?〉 .
[ #b #e #y #z #H // ] qed.

lemma ssb_step: ∀b, e, y, z,H. ssb (AppValue b e) y z H= AppValue (ssv b y z ?) (ssv e y z ?).
[ #b #e #y #z #H // ] qed.

lemma sse_epsilon: ∀y,z,H. sse Epsilon y z H = Epsilon.
// qed.

lemma sse_step1: ∀e,w,b,y,z,H. veqb y w = false → 
 sse (Snoc e [w ← b]) y z H = Snoc (sse e y z ?) [w ← ssb b y z ?].
[ 2: @(alpha_lemma7 … e w b H)
| 3: @(alpha_lemma8 … e w b H)
]
@Environment_simple_ind2
[ #w #b #y #z #H #H1 >sse_epsilon
 normalize >H1 normalize @refl
| #e * #d #f #HI #w #b #y #z #H #H1 normalize
  >H1 //
] qed.

lemma sse_step2: ∀e,b,y,z,H. 
 sse (Snoc e [y ← b]) y z H = Snoc (sse e y z ?) [z ← ssb b y z ?].
[ 2: @(alpha_lemma7 … e y b H)
| 3: @(alpha_lemma8 … e y b H)
]
@Environment_simple_ind2
[ #b #y #z #H >sse_epsilon
 normalize >veqb_true >if_t normalize @eq_f2 //
| #e * #d #f #HI #b #y #z #H normalize >veqb_true normalize //
] qed.
 

lemma ssc_size:
 (∀c, x, y. ∀(H: inb y c = false). c_size (ssc c x y H) = c_size c) ∧
  (∀b.∀x, y. ∀(H: inb_b y b = false). c_size_b (ssb b x y H) = c_size_b b) ∧
   (∀e.∀x, y. ∀(H: inb_e y e = false). c_size_e (sse e x y H) = c_size_e e) ∧
    (∀v.∀x, y. ∀(H: inb_v y v = false). c_size_v (ssv v x y H) = c_size_v v) ∧
     (∀s.∀x, y.  ∀(H: inb_s y s = false). c_size_s (sss s x y H) = c_size_s s).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #H 
  whd in match (ssc 〈b, e〉 ? ? ?); normalize >Hb >He @refl
| #v #H #x #y #HH normalize >H //
| #v #w #Hv #Hw #x #y #HH normalize >Hv >Hw //
| #z #x #y normalize cases (veqb z x) normalize //
| #z #c #H #x #y #HH normalize cases (veqb z x) normalize //
| #x #y normalize //
| #e * #y #b #He #Hs #x #z #HH normalize cases (veqb x y) normalize normalize in Hs; >Hs //
  normalize in HH; lapply HH cases veqb normalize [1,3: >if_monotone #abs destruct ]
  cases inb_b // >if_monotone #abs destruct
| #z #b #H #x #y #HH normalize >H //
] qed.

lemma ssc_id:
 (∀c, x. ∀(H: inb x c = false). (ssc c x x H) = c) ∧
  (∀b.∀x. ∀(H: inb_b x b = false). (ssb b x x H) = b) ∧
   (∀e.∀x. ∀(H: inb_e x e = false). (sse e x x H) = e) ∧
    (∀v.∀x. ∀(H: inb_v x v = false). (ssv v x x H) = v) ∧
     (∀s.∀x. ∀(H: inb_s x s = false). (sss s x x H) = s).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #HH normalize >Hb >He //
| #v #H #x #HH normalize >H //
| #v #w #Hv #Hw #x #HH normalize >Hv >Hw //
| #z #x #HH normalize
  cut (veqb z x = true ∨ veqb z x = false) // * #Htf >Htf //
  elim (veqb_true_to_eq z x) #Heq #_ lapply (Heq Htf) -Heq #Heq destruct //
| #z #c #H #x #HH normalize >H
  [ cut (veqb z x = true ∨ veqb z x = false) // * #Hzx >Hzx
    normalize //
  ]
  lapply HH normalize cases inb // >if_monotone #H @H
| #x normalize //
| #e * #y #b #He #Hs #x normalize #HH >He
  [ 2: lapply HH cases inb_e // normalize #H @H]
  normalize in Hs; >Hs
  [ 2: lapply HH cases inb_b
    [ >if_monotone >if_monotone #H @H
    | >if_then_true_else_false cases inb_e normalize // #abs destruct
    ]
  ] cases (veqb x y) in HH ⊢%; normalize // #HH normalize cases inb_e in HH;
    normalize #r destruct
| #z #b #H #x #HH normalize >H @refl
] qed.

lemma ssc_in:
 (∀c, x, y. ∀(H: inb y c = false). inb x c= false →  (ssc c x y H) = c) ∧
  (∀b.∀x, y. ∀(H: inb_b y b = false). inb_b x b = false → (ssb b x y H) = b) ∧
   (∀e.∀x, y. ∀(H: inb_e y e = false). inb_e x e = false → (sse e x y H) = e) ∧
    (∀v.∀x, y. ∀(H: inb_v y v = false). inb_v x v = false → (ssv v x y H) = v) ∧
     (∀s.∀x, y. ∀(H: inb_s y s = false). inb_s x s = false → (sss s x y H) = s).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #HH
  change with (orb ? ?) in match (inb ? ?);
  #H lapply (orb_false … H) * #Hb' #He' 
  normalize >(Hb x y … Hb')
  >(He x y … He') @refl
| #v #H #x #y normalize #HH #H' >(H x y HH H') @refl
| #v #w #Hv #Hw #x #y
  change with (orb ? ?) in match (inb_b ? ?);
  change with (orb ? ?) in match (inb_b ? ?);
  #HH #H lapply (orb_false … H) * #Hv' #Hw'
  lapply (orb_false … HH) * #Hv'' #Hw'' 
  normalize >(Hv … Hv'' Hv') >(Hw … Hw'' Hw') @refl
| #z #x #y normalize #H #HH >veqb_comm >HH normalize @refl
| #z #c #H #x #y
  change with (orb ? ?) in match (inb_v ? ?);
  change with (orb ? ?) in match (inb_v ? ?);
  #HH #H lapply (orb_false … H) -H * #Hz' #Hc'
  lapply (orb_false … HH) * #Hz'' #Hc''
  normalize >( veqb_comm z x) >Hz' normalize >(H … Hc'' Hc') @refl
| #x #y normalize #_ #_ @refl
| #e * #y #b #He #Hs #x #z
  change with (orb ? ?) in match (inb_e ? ?); #HH
  change with (orb ? ?) in match (inb_e ? ?); #H
  lapply (orb_false … H) * #He' #Hs'
  lapply (orb_false … HH) * #He'' #Hs'' normalize in Hs;
  normalize >(He … He'' He') >(Hs … Hs'' Hs')
  cut (veqb x y = false)
  [ lapply Hs' normalize cases veqb // >if_t #H @H ]
   #Hveq >Hveq normalize @refl  
| #z #b #HI #x #y 
  change with (orb ? ?) in match (inb_s ? ?); #HH
  change with (orb ? ?) in match (inb_s ? ?); #H
  lapply (orb_false … H) * #Hz' #Hb'
  lapply (orb_false … HH) * #Hz'' #Hb'' 
  normalize @eq_f >(HI … Hb'' Hb') @refl
] qed.
(*
lemma domb_sse_inv: ∀e, x, y, z. ∀H. domb_e x (sse e y z H)  = domb_e x e.
@Environment_simple_ind2
[ normalize //
| #e * #w #b #HI #x #y #z
  #H
  whd in match (sse ? ? ? ?);
  cut (veqb y w = true ∨ veqb y w = false) // * #Hyw >Hyw normalize
  cut (veqb x w = true ∨ veqb x w = false) // * #Hxw >Hxw normalize //
  cut (veqb x z = true ∨ veqb x z = false) // * #Hxz >Hxz normalize //
  >HI //
] qed.
*)
lemma alpha_fin1:
(∀c,x,y,z,H. inb z c= false → veqb x z= false
                            → inb z (ssc c y x H) = false) ∧
 (∀b,x,y,z,H. inb_b z b= false → veqb x z= false
                             → inb_b z (ssb b y x H) = false) ∧
  (∀e,x,y,z,H. inb_e z e= false → veqb x z= false
                              → inb_e z (sse e y x H) = false) ∧
   (∀v,x,y,z,H. inb_v z v= false → veqb x z= false
                               → inb_v z (ssv v y x H) = false) ∧
    (∀s,x,y,z,H. inb_s z s= false → veqb x z= false
                                → inb_s z (sss s y x H) = false).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #z #H #H1 #H2
  normalize
  >(Hb x y z) // [ 2: lapply H1 normalize cases inb_b // >if_t #H @H ]
  >(He x y z) // lapply H1 normalize cases inb_e // >if_monotone #H @H
| #v #HI normalize @HI
| #v #w #Hv #Hw #x #y #z #H #H1 #H2 normalize
  >Hv // [ 2: @(alpha_lemma4 … w … H1) ]
  >Hw // @(alpha_lemma5 … v … H1)
| #w #x #y #z normalize
  cut (veqb w y = true ∨ veqb w y = false) // * #Htf >Htf normalize
  [ #H1 #H2 #H3 >veqb_comm //
  | #H1 #H2 #H3 @H2
  ]
| #w #c #Hc #x #y #z #H #H1 #H2 normalize
  cut (veqb w y = true ∨ veqb w y = false) // * #Hwy >Hwy normalize
  [ @H1
  | cut (veqb z w = false)
    [ lapply H1 normalize cases veqb // >if_t #H @H ]
    #Hzw >Hzw >if_f >Hc // lapply H1 normalize cases inb // >if_monotone #H @H
  ]
| //
| #e * #w #b #He #Hs #x #y #z #H #H1 #H2
  whd in match (inb_e x ?) in H;
  change with (orb ? ?=false) in H;
  lapply (orb_false … H) * #H' #H''
  whd in match (inb_e z ?) in H1;
  change with (orb ? ?=false) in H1;
  lapply (orb_false … H1) * #H1' #H1''
  normalize
  cut (veqb y w = true ∨ veqb y w = false) // * #Hyw >Hyw normalize
  [ >He // >if_f normalize in Hs; >veqb_simm >H2 >if_f
    lapply (Hs x y z H'' H1'' H2)
    cut (veqb z w = false)
    [ lapply H1'' normalize cases veqb normalize //]
    #Hzw >Hzw >if_f #Hs'' >Hs'' @refl
  | >He // normalize normalize in Hs; >Hs // [ @H1'' | @H'']
  ]
| #w #b #Hb #x #y #z #H #H1 #H2 normalize >Hb //
  [ lapply H1 normalize cases veqb normalize //
  | lapply H1 normalize cases inb_b // >if_monotone #H @H
  ]
] qed.

(*
lemma ssc_in:
 (∀c, x, y, z. fvb x (ssc c y z) =
             match (veqb x y) with
              [ true ⇒  fvb x c ∧ veqb x z
              | false ⇒ fvb x c ∨ (fvb y c ∧ veqb x z)
              ]) ∧
  (∀b.∀x, y, z. fvb_b x (ssb b y z) =
             match (veqb x y) with
              [ true ⇒  fvb_b x b ∧ veqb x z
              | false ⇒ fvb_b x b ∨ (fvb_b y b ∧ veqb x z)
              ]) ∧
   (∀e.∀x, y, z. fvb_e x (sse e y z) =
             match (veqb x y) with
              [ true ⇒  fvb_e x e ∧ veqb x z
              | false ⇒ fvb_e x e ∨ (fvb_e y e ∧ veqb x z) (*z può venire catturato da sostituzioni
                                                             a destra del punto dove avviene la sostituzione*)
              ]) ∧
    (∀v.∀x, y, z. fvb_v x (ssv v y z) =
             match (veqb x y) with
              [ true ⇒  fvb_v x v ∧ veqb x z
              | false ⇒ fvb_v x v ∨ (fvb_v y v ∧ veqb x z)
              ]) ∧
     (∀s.∀x, y, z. fvb_s x (sss s y z) =
             match (veqb x y) with
              [ true ⇒  fvb_s x s ∧ veqb x z
              | false ⇒ fvb_s x s ∨ (fvb_s y s ∧ veqb x z)
              ]).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #z
  whd in match (ssc ???);
  whd in match (fvb ? ?);
  >Hb >He
  whd in match (fvb ? 〈b, e〉);
  whd in match (fvb y 〈b, e〉);
  cut (veqb x y = true ∨ veqb x y = false) // * #Htf
  [ >Htf normalize >domb_sse_inv
    cut (veqb x z = true ∨ veqb x z = false) // * #Hxz >Hxz normalize
    [ >if_then_true_else_false >if_then_true_else_false
      >if_then_true_else_false //
    | >if_monotone >if_f >if_monotone >if_monotone //
    ]
  | >Htf >if_f >if_f >if_f >domb_sse_inv
    cases domb_e normalize
    [ >if_monotone >if_f >if_monotone >if_f
      cases fvb_e // normalize cases veqb
      [ 2: >if_monotone >if_monotone // ]
      >if_then_true_else_false >if_then_true_else_false
      cases fvb_e [ >if_monotone // ]
      >if_then_true_else_false
    | >if_then_true_else_false >if_then_true_else_false
      
    [ >if_then_true_else_false >if_then_true_else_false >if_then_true_else_false
      cases (fvb_b) normalize
      [ cases domb_e normalize // 
      |
    | >if_monotone >if_monotone >if_monotone >if_then_true_else_false
      >if_then_true_else_false >if_then_true_else_false //
    ]
  ]


let rec alpha0 b e n (l:nat) on l: e_size e = l → Bite×Environment ≝
 match l return λl. e_size e = l → Bite×Environment with
 [ O ⇒  match e return λe. e_size e = O → Bite×Environment with
       [ Epsilon ⇒ λp. (mk_Prod Bite Environment b Epsilon) 
       | Snoc e' s ⇒ λp. ?
       ]
 | S m ⇒ match e return λe. e_size e = S m → Bite×Environment with 
   [ Epsilon ⇒ λp. ?
   | Snoc e' s ⇒ λp. match s with
     [ subst y b' ⇒ let z ≝ ((alpha0 (ssb b y νn) (sse e' y νn) (S n) m) ?) in 
       mk_Prod Bite Environment (\fst z)
       (Snoc (\snd  z) (subst (νn) (ssb b' y (νn))))
     ]
   ]
 ].
 
[ @(alpha_lemma1 e' s p)
| @(alpha_lemma2 m p)
| @(alpha_lemma3 e' s m y n p)
] qed.

definition alpha2 ≝ 
 λc.λn. match c with
  [ CCrumble b e ⇒ 
  〈\fst (alpha0 b e n (e_size e) (refl nat …)), 
   \snd (alpha0 b e n (e_size e) (refl nat …))〉
  ].
*)

lemma alpha_aux1:  ∀b,e',s,n. (fresh_var 〈b,Snoc e' s〉≤n) → (fresh_var 〈b,e'〉≤S n).
#b #e #s #n  change with (max ? ?) in match (fresh_var ?);
change with (max ? ?) in match (fresh_var ?);
change with (max ? ?) in match (fresh_var_e ?); #p @to_max
  [ @le_S @(le_maxl … p)
  | @le_S @(le_maxl … (le_maxr … p))
  ]
qed.

lemma alpha_aux2: ∀b,n.∀m:ℕ.fresh_var 〈b,Epsilon〉≤m∧m<n→inb (νm) 〈b,Epsilon〉=false.
#b #n #m * #H1 #H2 normalize lapply fresh_var_to_in_crumble * * * *
#_ #Hfvb #_ #_ #_ >Hfvb // lapply H1 
change with (max ? ?) in match (fresh_var ?); -H1 #H1 @(le_maxl … H1) qed.

lemma alpha_aux3:
 ∀b, e', a, n, y, b'. (∀m:ℕ.fresh_var 〈b,e'〉≤m∧m<S n→inb (νm) a=false) →
  (fresh_var 〈b,Snoc e' [y←b']〉≤n) →
   (inb (νn) a=false).

#b #e' #a #n #y #b' #h #p @h % // 
lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
lapply (Hdc … p) * #Hb #He
lapply (Hde … He) * -He #He #Hs
change with (max ? ? ≤n)
@to_max // qed.

lemma alpha_aux4:
 ∀b, e', a, n, y, b', K.
  ∀(h:(∀m:ℕ.fresh_var 〈b,e'〉≤m∧m<S n→inb (νm) a=false)).
   ∀p: (fresh_var 〈b,Snoc e' [y←b']〉≤n).
   (∀m:ℕ.fresh_var 〈b,Snoc e' [y←b']〉≤m∧m<n
     →inb (νm) (at (ssc a y (νn) K) (Snoc Epsilon [νn←b']))
    =false).

#b #e' #a #n #y #b' #K #h #p
#m #H cut (∀K. inb (νm) (at (ssc a y (νn) (K…)) (Snoc Epsilon [νn ← b']))= false) [2: #UU @UU]
  lapply h -h
  cases a #r #t #h #K'
  whd in match (ssc (CCrumble r t) y (νn) K');
  whd in match (at ? ?);
  whd in match (concat ? ?);
  >concat_e_epsilon
  whd in match (inb ? ?);
  cut (inb (νm) 〈r,t〉=false)
  [ lapply (h m) -h #h @h % [ 2: elim H #H1 #H2 /2/]
    elim H #H1 #_
    lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
  lapply (Hdc … H1) * #Hb #He
  lapply (Hde … He) * -He #He #Hs
  change with (max ? ?≤?) @to_max //
  ] -h #h
  cut (neqb m n=false)
  [ elim H #_ cut (neqb n m =true ∨ neqb n m =false) // * //
    elim (neqb_iff_eq n m) #Heq #_ #Hnm lapply (Heq Hnm) -Heq #Heq destruct
    normalize #abs @False_ind lapply abs @le_Sn_n
  ]
  #Hf
  lapply alpha_fin1 * * * * #_ #Hbb #Hee #_ #_
  >Hbb // [ 2: lapply h normalize cases inb_b // >if_t #H @H ]
  whd in match (inb_e ? ?);
  >(Hee) // [ 2: lapply h normalize cases inb_e // >if_monotone #H @H ]
  >if_f normalize >Hf >if_f
  lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
  elim H -H #H #_
  lapply (Hdc … H) * #_ #He
  lapply (Hde … He) * #_ #Hs
  lapply (Hds … Hs) * #_ lapply (fresh_var_to_in_crumble)
  * * * * #_ #Hfvb #_ #_ #_ @Hfvb
qed.

let rec alpha (b: Bite) (e: Environment) (n: nat) on e:
 fresh_var 〈b, e〉 ≤ n → 
  Σc. ∀m. fresh_var 〈b, e〉 ≤ m ∧ m < n → inb (νm) c = false ≝ 
 match e return λe. fresh_var 〈b, e〉 ≤ n → Σc. ∀m. fresh_var 〈b, e〉 ≤ m ∧ m < n → inb (νm) c = false  with
 [ Epsilon ⇒ λp. mk_Sig … 〈b, Epsilon〉 (alpha_aux2 b n)
 | Snoc e' s ⇒ match s return λs. fresh_var 〈b, Snoc e' s〉 ≤ n → Σc. ∀m. fresh_var 〈b, Snoc e' s〉 ≤ m ∧ m < n → inb (νm) c = false with 
   [subst y b' ⇒ λp. match alpha b e' (S n) (alpha_aux1 … (subst y b') … p) with
     [ mk_Sig a h ⇒ mk_Sig …(at (ssc (a) y (νn) (alpha_aux3 b e' a n y b' h p)) (Snoc Epsilon (subst (νn) b'))) (alpha_aux4 b e' a n y b' (alpha_aux3 b e' a n y b' h p) h p) ]
   ]
 ]
.

let rec alpha2 (b: Bite) (e: Environment) (n: nat) on e:
 fresh_var 〈b, e〉 ≤ n → 
  Σc. ∀m. fresh_var 〈b, e〉 ≤ m ∧ m < n → inb (νm) c = false ≝ 
 match e return λe. fresh_var 〈b, e〉 ≤ n → Σc. ∀m. fresh_var 〈b, e〉 ≤ m ∧ m < n → inb (νm) c = false  with
 [ Epsilon ⇒ λp. mk_Sig … 〈b, Epsilon〉 (alpha_aux2 b n)
 | Snoc e' s ⇒ match s return λs. fresh_var 〈b, Snoc e' s〉 ≤ n → Σc. ∀m. fresh_var 〈b, Snoc e' s〉 ≤ m ∧ m < n → inb (νm) c = false with 
   [subst y b' ⇒ λp. mk_Sig …(at (ssc (pi1 … (alpha2 b e' (S n) (alpha_aux1 … (subst y b') … p))) y (νn) (alpha_aux3 b e' ? n y b' ? p)) (Snoc Epsilon (subst (νn) b'))) (alpha_aux4 b e' ? n y b' (alpha_aux3 b e' ? n y b' (pi2 … (alpha2 b e' (S n) (alpha_aux1 … (subst y b') … p))) p) (pi2 … (alpha2 b e' (S n) (alpha_aux1 … (subst y b') … p))) p) ]
 ]
.

lemma alpha_eq: ∀e, b, n, H. alpha b e n H = alpha2 b e n H.
@Environment_simple_ind2
[ //
| #e *#y #b'  #HI #b #n #H whd in match (alpha ? ? ? ?);
  whd in match (alpha2 ? ? ? ?);
  lapply (HI b (S n) (alpha_aux1 b e [y←b'] n H))
  cases (alpha b e (S n) (alpha_aux1 b e [y←b'] n H)) * #bb #ee #hh
  whd in match (match ? in Sig with [_⇒ ?]);
  whd in match (at ? ?); #Heq <Heq //
] qed. 

 
(*  
let rec alpha (b: Bite) (e: Environment) (n: nat) on e: fresh_var 〈b, e〉 ≤ n → Crumble ≝ 
 match e return λe. fresh_var 〈b, e〉 ≤ n → Crumble  with
 [ Epsilon ⇒ λp. 〈b, Epsilon〉
 | Snoc e' s ⇒ match s return λs. fresh_var 〈b, Snoc e' s〉 ≤ n → Crumble with 
   [subst y b' ⇒ λp. at (ssc (alpha b e' (S n) (alpha_aux1 … (subst y b') … p)) y (νn) ?) (Snoc Epsilon (subst (νn) b'))]
 ]
.

lapply p -p @(Environment_simple_ind2 … e')
[ #p
  cut (∀K. inb (νn) (alpha b Epsilon (S n) (K …))=false )
  [ 2: #UU @UU] #H
| #e' #s #HI #H

lemma k_domain_sse_interval_dom: ∀e,x,n,y.
 interval_dom e (S n) → 
  domb_e y e=true →
   domb_e y (sse e x (νn)) = true.

@Environment_simple_ind2
[ #x #n #y normalize #_ #abs destruct
| #e * * #z #b #HI * #x #n * #y #Ha lapply (HI (νx) n (νy) (interval_lemma … Ha))
  #HI' #Hb
  whd in match (sse ? ? ?);
  check domb_e
  change with (match (sss [νz←b] (νx) νn) with 
     [subst (y:Variable)   (b:Bite)⇒veqb ? ?∨domb_e ? (sse e (νx) (νn))])
   in match (domb_e (νy) (Snoc (sse ? ? ?) (sss ? ? ?)));
   whd in match (sss ? ? ?);
   whd in match (veqb ? ?);
   normalize
   cut (neqb z x = true ∨ neqb z x = false) // * #Hzx >Hzx normalize
   [ lapply (neqb_iff_eq z x) * #Heq #_ lapply (Heq Hzx) -Heq #Heq
     destruct
     cut (neqb y n = true ∨ neqb y n = false) // * #Hyn >Hyn normalize //
     cut (neqb y x = true ∨ neqb y x = false) // * #Hyx >Hyx normalize
    | normalize
      cut (neqb y z = true ∨ neqb y z = false) // * #Hyz >Hyz normalize //
      normalize in Hb; >Hyz in Hb; >if_f #Hll @HI' @Hll
    ] 
      
   >HI' [ normalize >if_monotone //]
   lapply (Ha y) lapply Hb normalize normalize normalize in Hb;
*)
lemma did_aux1:
 ∀e,x,y,z,H. domb_e (νx) e= false → 
  neqb x y = false →
   neqb x z = false → 
    domb_e (νx) (sse e (νy) (νz) H)=false.

@Environment_simple_ind2
[ #x #y #z normalize //
| #e * * #y #b #HI #x #w #z #H
(*  lapply (HI x w z)*)
  whd in match (sse (Snoc ? ?) ? ?);
  whd in match (domb_e ? (Snoc ? ?));
  whd in match (domb_e ? (Snoc ? ?));
  >veqb_comm whd in match (veqb ? ?);
  cut (neqb y x = true ∨ neqb y x = false) // * #Hyx >Hyx normalize
[ #abs destruct
| #H1 #H2 #H3 >(HI … H1 H2 H3) [ 2: lapply H normalize cases inb_e // >if_t // ]
  cases (neqb w y) normalize >H3 normalize >HI //
  >if_then_true_else_false >neq_simm >Hyx @refl
]
] qed.

lemma did_aux:
 ∀e,x,y,z,H. domb_e x e= false → 
  domb_e y e = false →
   domb_e z (sse e x y H)=domb_e z e.
@Environment_simple_ind2
[ //
| #e * * #w #b #HI * #x * #y * #z #H #H1 #H2 
  normalize
  cut (neqb x w = false)
  [ lapply H1 normalize cases neqb // >if_t #H @H ]
  #Hxw >Hxw normalize >(HI (νx) (νy) (νz))
  [ @refl
  | lapply H2 normalize cases domb_e // >if_monotone #H @H
  | lapply H1 normalize cases domb_e // >if_monotone #H @H ]
] qed.

lemma did_aux2:
 ∀e,x,y,H. domb_e x e= false → 
  domb_e y e = false →
   domb_e y (sse e x y H)=false.
/2/ qed.

lemma did_aux3:
 ∀e,x,y,H. domb_e x e= false → 
  domb_e y e = false →
   domb_e y (sse e y x H)=false.
/2/ qed.

lemma dist_dom_switch: ∀e,s,t.
 dist_dom (Snoc (Snoc e s) t) = true  →  
  dist_dom (Snoc (Snoc e t) s) = true.

@Environment_simple_ind2
[ * #a #b * #c #d normalize >veqb_comm cases veqb normalize //
| #e * * #a #b #HI * * #c #d * * #f #g #H
  cut (dist_dom e = true)
  [ >(dist_dom_conservative … [νa ←b]) // 
    >(dist_dom_conservative … [νc ←d]) //
    >(dist_dom_conservative … [νf ←g]) //
  ] #Hdde
  cut (domb_e (νf) e = false)
  [ lapply H normalize cases domb_e // >if_monotone >if_monotone >if_t >if_f #H
    >H @refl ]
  #Hdf
  cut (domb_e (νc) e = false)
  [ lapply H normalize cases (domb_e (νc) e) // >if_monotone >if_t >if_f
    >if_monotone #H >H @refl ]
  #Hdc
  cut (domb_e (νa) e = false)
  [ lapply H normalize cases (domb_e (νa) e) // >if_t >if_f >if_monotone
    >if_monotone #H >H @refl ]
  #Hda
  lapply H
  lapply (HI [νc←d] [νf←g]) normalize
  >neq_simm >Hdde >Hdf >Hdc >Hda normalize
  >if_then_true_else_false
  >if_then_true_else_false
  >if_then_true_else_false
  >if_then_true_else_false
  >if_then_true_else_false
  >if_then_true_else_false
  cut (neqb c f = true ∨ neqb c f = false) // * #Hcf >Hcf normalize
  [ #_ #H @H
  | #_ cases neqb cases neqb //
  ]
] qed.

  
lemma dom_al_aux1:∀e,y,n,z,b,H.
  (dist_dom (Snoc e [z←b])=true) →
   veqb y z=false →
    veqb (νn) z=false →
     (domb_e z (sse e y (νn) H)=false).

@Environment_simple_ind2
[ //
| #e * * #w #b' #HI * #y #n * #z #b #H #Hddom
  cut (dist_dom (Snoc e [νz←b])=true)
  [ >(dist_dom_conservative … [νw ← b']) // >dist_dom_switch // ]
  #Hd lapply Hddom -Hddom
 whd in match (dist_dom ?);
  whd in match (match ? in Substitution with [_⇒?]);
  #Hddom
  cut (domb_e (νz) (Snoc e [νw ← b'])=false)
  [ lapply Hddom cases domb_e normalize //]
  #Hdomb
  cut (dist_dom (Snoc e [νw←b'])=true)
  [ lapply Hddom >Hdomb normalize //]
  #Hddom' normalize
  cases (neqb y w) normalize
  [ #Hyz #Hnz >neq_simm >Hnz >if_f >(HI …) //
  | #Hyz #Hnz  >HI // lapply Hdomb normalize cases neqb //
  ]
] qed.

lemma dom_al_aux2:∀e,z,n,H.
  (interval_dom e (S n)) →
   (domb_e z e = false) →
    (domb_e (νn) (sse e z (νn) H)=false).
     
@Environment_simple_ind2
[ //
| #e * * #w #b' #HI * #z #n #H #Hddom #Hin
  normalize 
  cut (neqb z w = false)
  [ lapply Hin normalize cases neqb // >if_t #H @H ]
  #Hzw >Hzw normalize
  cut (neqb n w = false)
  [ lapply H normalize cases neqb // >if_t >if_monotone #H @H ]
  #Hnw >HI >Hnw //
  [ lapply Hin normalize cases domb_e // >if_monotone #H @H
  | @(interval_lemma … [νw ←b'] Hddom)
  ]
] qed.

lemma dist_interval_dom: ∀e,n,y,H.  dist_dom e=true → (interval_dom e (S n)) → dist_dom (sse e y (νn) H)=true.

@Environment_simple_ind2
[ //
| #e * * #z #l #HI #n * #y #H #Ha #Hb
  whd in match (sse ? ? ? ?);
  whd in match (veqb ? ?);
  cut (inb_e (νn) e = false)
  [ lapply H normalize cases inb_e // normalize #H @H ]
  #HH
  cut (neqb y z = true ∨ neqb y z = false) // * #Hyz >Hyz
  [ >if_t normalize >HI
    [ >if_then_true_else_false
      elim (neqb_iff_eq y z) #Heq #_ lapply (Heq Hyz) -Heq #Heq destruct 
      cut (neqb n z = false)
      [ lapply H normalize cases neqb // normalize >if_monotone #H @H ]
      #Hnz >dom_al_aux2 //
      [ lapply Ha normalize cases domb_e normalize //
      | @(interval_lemma … [νz ←l] Hb)
      ]
    | 2: @(interval_lemma … [νz ← l]) @Hb
    | 3: @(dist_dom_conservative … [νz ← l] Ha)
    ]
  | normalize >HI
    [ >if_then_true_else_false
      >dom_al_aux1 // lapply H normalize cases neqb // >if_t >if_monotone #H @H
    | 2: @(interval_lemma … [νz ← l]) @Hb
    | 3: @(dist_dom_conservative … [νz ← l] Ha)
    ]
  ]
] qed.



lemma size_alpha: ∀b,e.∀n.∀(H:fresh_var 〈b, e〉≤n). c_size (pi1 … (alpha b e n H)) = c_size 〈b, e〉.
#b @(Environment_simple_ind2 )
[ normalize //
| #e' * #y #b' #HI #n #H
  whd in match (alpha ? ? ? ?); lapply ssc_size * * * * #Hsc #_ #_ #_ #_
  lapply (HI (S n)) cases ((alpha b e' (S n))) * #f #g #KK 
  whd in match ( match «〈f,g〉,?»
      in Sig
      with 
     [mk_Sig a h⇒
      «at (ssc a y (νn) (alpha_aux3 b e' a n y b' h H)) (Snoc Epsilon [νn←b']),
      alpha_aux4 b e' a n y b' (alpha_aux3 b e' a n y b' h ?) h H»]);
  >c_size_at >Hsc #H' >H'
  [ normalize //
  | lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
  lapply (Hdc … H) * #Hb #He
  lapply (Hde … He) * -He #He #Hs
  @to_max @le_S //
] qed.
 
lemma w_well_named_alpha: 
 ∀b, e. ∀n. ∀H: fresh_var 〈b,e〉 ≤ n. 
  (w_well_named (pi1 … (alpha b e n H))=true) ∧ interval_dom match (pi1 … (alpha b e n H)) with [CCrumble b e ⇒ e] n.

#b @Environment_simple_ind2
[ #n normalize #_ % // #x #abs destruct
| #e * * #y #b' #HI #n #H
  lapply (HI (S n) (le_S … (transitive_le … (fresh_var_cons_bes b e [νy ←b']) H)))
  whd in match (alpha b (Snoc e [νy←b']) n H);
  cases alpha * #b'' #e' #HH
  whd in match ( match «〈b'',e'〉,?»
    in Sig
    with 
   [mk_Sig a h⇒
    «at (ssc a (νy) (νn) (alpha_aux3 b e a n (νy) b' h H)) (Snoc Epsilon [νn←b']),
    alpha_aux4 b e a n (νy) b' (alpha_aux3 …) h H»]);
  >ssc_step
  whd in match (match ? in Crumble with [_ ⇒ ?]);
  whd in match (match ? in Crumble with [_ ⇒ ?]);
  * #Ha #Hb
  whd in match (w_well_named …);
  change with (dist_dom ?) in match ((λc:Crumble .(match c in Crumble return λ_:Crumble.bool with [_⇒?])) (CCrumble ? ?));
  whd in match (concat ? ?);
  whd in match (sse …);
  >concat_e_epsilon
  whd in match (dist_dom ?);
  >dist_interval_dom [ 2: @Hb | 3: @Ha]
  >if_then_true_else_false
  %
  [ >(did_aux2 … ) //
    [ lapply (Hb n) cases domb_e // #H @False_ind @(le_Sn_n n) @H @refl
    | lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
      lapply (Hdc … H) * #Hfvb #Hfve
      lapply (Hde … Hfve) * -Hfve #Hfve #Hfvs
      lapply (Hds … Hfvs) * -Hfvs #Hy #Hfvb'
      cut (domb_e (νy) e'=true ∨domb_e (νy) e'=false) // * //
      #Habs @False_ind lapply (Hb … Habs) #Hy'
      lapply (le_S … Hy') -Hy' #Hy'
      lapply (transitive_le … Hy' Hy)
      @le_Sn_n
    ]
  | #z cut (neqb z n = true ∨ neqb z n = false) // * #Hzn >Hzn normalize
    [ #_ elim (neqb_iff_eq z n) #Heq #_ lapply (Heq Hzn) -Heq #Heq destruct //
    | >did_aux
      [ 2: lapply (Hb n) cases domb_e // #H @False_ind @(le_Sn_n n) @H @refl
      | 3: lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
           lapply (Hdc … H) * #Hfvb #Hfve
           lapply (Hde … Hfve) * -Hfve #Hfve #Hfvs
           lapply (Hds … Hfvs) * -Hfvs #Hy #Hfvb'
           cut (domb_e (νy) e'=true ∨domb_e (νy) e'=false) // * //
           #Habs @False_ind lapply (Hb … Habs) #Hy'
           lapply (le_S … Hy') -Hy' #Hy'
           lapply (transitive_le … Hy' Hy)
           @le_Sn_n
      | >Hzn >if_f #H lapply (Hb … H) -H #H  lapply (le_S … H) /2/
      ]
    ]
  ]
] qed.

lemma well_named_alpha: 
 ∀f, b, e. ∀n. fresh_var (at 〈b, e〉  f) ≤ n → 
  match (at 〈b, e〉 f) with [ CCrumble b e ⇒ ∀H. (w_well_named (pi1 … (alpha b e n H))=true) ∧ interval_dom match (pi1 … (alpha b e n H)) with [CCrumble b e ⇒ e] n].

@Environment_simple_ind2
[ #b #e whd in match (at ? ?); >concat_e_epsilon #n #H
  whd in match (match ? in Crumble with [_⇒ ?]); @w_well_named_alpha
| #f * * #y #b' #HI #b #e #n #H
  lapply (HI b e (S n))
  whd in match (at ? ?);
  whd in match (at ? ?);
  whd in match (concat ? (Snoc ? ?));
  whd in match (match ? in Crumble with [_ ⇒?]);
  whd in match (match ? in Crumble with [_ ⇒?]);
  whd in match (alpha b (Snoc ? ?) ? ?);
  [ 2: @H]
  cases alpha
  [ 2: lapply H whd in match (at ? ?); whd in match (concat ? ?);
    lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #_ #H
    lapply (Hdc … H) * #Hfvb #Hfve
    lapply (Hde … Hfve) * -Hfve #Hfve #Hfvs
    @to_max @le_S [ @Hfvb | @Hfve ]
  ] * #t #u #KK
   whd in match ( match «CCrumble t u,?»
    in Sig
    with 
   [mk_Sig a h⇒ «at (ssc a (νy) (νn) (alpha_aux3 b (concat ??) a n (νy) b' h H))(Snoc Epsilon [νn←b']),
       alpha_aux4 b (concat ??) a n (νy) b' (alpha_aux3 …) h H»]);
  whd in match (match ? in Crumble return λ_:Crumble.Environment with [_⇒?]);
  #HI'
  lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds #H'
  lapply (Hdc … H) * #Hfvb #Hfve
  lapply (Hde … Hfve) * -Hfve #Hfve #Hfvs
  lapply (Hds … Hfvs) * -Hfvs #Hy #Hfvb'
  cut (fresh_var 〈b,concat e f〉≤S n)
  [ @le_S change with (max ? ?) in match (fresh_var ?); @to_max // ]
  -H -Hdc -Hde -Hds #H lapply (HI' H H) * #Ha #Hb
  >ssc_step whd in match (w_well_named ?);
  >did_aux2
  [ 2: lapply (Hb n) whd in match (match ? in Substitution with [_⇒ ?]);
   cases domb_e // #H @False_ind @(le_Sn_n n) @H @refl
  | 3: lapply (Hb y) cases domb_e // #H @False_ind @(le_Sn_n n)
       lapply (le_S … (H (refl …))) -H #H @(transitive_le … H Hy)
  ]
  whd in match (¬false);
  >if_t
  >dist_interval_dom
  [ 2: @Hb
  | 3: @Ha
  ] % //
  #z cut (neqb z n = true ∨ neqb z n = false) // * #Hzn >Hzn
  whd in match (match ?  in Crumble return λ_:Crumble.Environment with [_⇒?]);
  [ #_ elim (neqb_iff_eq z n) #Heq #_ lapply (Heq Hzn) -Heq #Heq destruct //
  | whd in match (concat ? ?); whd in match (domb_e ? (Snoc ? ?) ); >did_aux
    [ 2: lapply (Hb n) cases domb_e // #H @False_ind @(le_Sn_n n) @H @refl
    | 3: lapply (Hb y) cases domb_e // #H @False_ind @(le_Sn_n n)
         lapply (le_S … (H (refl …))) -H #H @(transitive_le … H Hy)
    | whd in match (veqb ? ?); >Hzn >if_f #H lapply (Hb … H) -H #H  lapply (le_S … H) /2/
    ]
  ]
] qed.

lemma domb_sse: ∀e, x, y, y', H. domb_e x (sse e y y' H) = true  →
 domb_e x e = true ∨ (domb_e y e = true ∧ veqb x y' = true).
@Environment_simple_ind2
[ #x #y #y' #H normalize #abs destruct
| #e * * #z #b' #HI #x #y #y' #H
  whd in match (sse ? ? ? ?);
  cut (veqb y (νz) = true ∨ veqb y (νz) = false) // * #Htf
  [ >Htf normalize >Htf >if_t elim (veqb_true_to_eq y (νz)) #Heq #_
    lapply (Heq Htf) -Heq #Heq destruct
    cut (veqb x y' = true ∨ veqb x y' = false) // * #Hxy' >Hxy'
     // >if_f #HH
    lapply (HI … HH) *
    [ * >if_monotone @or_introl @refl ] * * * >Hxy' @or_intror % //
  | >Htf >if_f whd in ⊢ ((? ? % ?) → ?);
    whd in match (domb_e ? (Snoc ? ?)); cases veqb normalize
    [ #_ @or_introl //
    | #HH lapply (HI … HH) * * [ @or_introl @refl ] * *
      >if_monotone @or_intror % @refl
    ]
  ]
] qed.

let rec beta c n on c: list (Variable×Variable) ≝ 
 match c with
  [ CCrumble b e ⇒ beta_e e n ]

and beta_e e n on e: list (Variable×Variable) ≝ 
 match  e with
  [ Epsilon ⇒ nil ?
  | Snoc e s ⇒ match s with
   [ subst y b ⇒ cons ? (mk_Prod … y (νn)) (beta_e e (S n)) ]
  ]
  .
  
  
let rec rhs (l: list (Variable×Variable)) (x:Variable) on l:Prop  ≝ 
 match l with
 [ nil ⇒ False
 | cons h t ⇒ match h with
  [ mk_Prod y s ⇒ (veqb x s = true) ∨ (rhs t x) ]
 ] 
.

let rec distinct_rhs (l: list (Variable×Variable)) on l ≝ 
 match l with
 [ nil ⇒ True
 | cons h t ⇒ match h with [ mk_Prod y y' ⇒ ¬(rhs t y') ∧ distinct_rhs t ]
 ] .
 
lemma beta_aux1: ∀e, n, m. m > n →  ¬(rhs (beta_e e m) νn).
@Environment_simple_ind2
[ #n #m normalize #_ % //
| #e * #y #b #HI #n normalize #m #H cut (neqb n m = false)
  [ cut (neqb n m = true ∨ neqb n m = false) // * #Hnm //
    elim (neqb_iff_eq n m) #Heq #_ lapply (Heq Hnm) -Heq #Heq destruct
    @False_ind lapply H @le_Sn_n ]
  #HH >HH % * [ #abs destruct ] #HHH elim (HI n (S m) ?) [ #HII @(HII HHH) ]
  normalize @(le_S … H)
] qed.

lemma distinct_rhs_beta_e: ∀e, n. distinct_rhs (beta_e e n).
@Environment_simple_ind2 // #e * #y #b' #HI #n
whd in match (beta ? ?); normalize % // % #HH elim (beta_aux1 e n (S n))
[ #HHH @(HHH HH)] normalize // qed.

 
lemma distinct_rhs_beta: ∀c, n. distinct_rhs (beta c n).
* #b @Environment_simple_ind2 // #e * #y #b' #HI #n
whd in match (beta ? ?); normalize % // % #HH elim (beta_aux1 e n (S n))
[ #HHH @(HHH HH)] normalize // qed.


lemma gamma_aux1: ∀c, y, y', t.∀(H : ((∀x:Variable.rhs (〈y,y'〉::t) x→inb x c=false)∧distinct_rhs (〈y,y'〉::t))).
 ((∀x:Variable.rhs t x→inb x c=false)∧distinct_rhs t).
#c #y #y' #t #H %
  [ #k #HH elim H #HHH #_ @HHH normalize @or_intror @HH
  | elim H #_ normalize * #_ //
  ]
qed.

lemma gamma_aux2: ∀c. ∀(H : ((∀x:Variable.rhs [] x→inb x c=false)∧distinct_rhs [])).  
 (∀x:Variable.inb x c=false→¬rhs [] x→inb x c=false).
#c #H #k #HH #_ @HH qed.

lemma gamma_aux3:  
∀(gamma :
  (∀l:list (Variable×Variable)
   .∀c:Crumble
    .(∀x:Variable.rhs l x→inb x c=false)∧distinct_rhs l
     →Σd:Crumble.(∀x:Variable.inb x c=false→¬rhs l x→inb x d=false))).
 ∀(c : Crumble).
 ∀(t : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::t) x→inb x c=false)∧distinct_rhs (〈y,y'〉::t))).
 (inb y'
  (pi1 Crumble (λd:Crumble.∀x:Variable.inb x c=false→¬rhs t x→inb x d=false)
   (gamma t c (gamma_aux1 c y y' t H)))
  =false).
#gamma #c #t #y #y' #H cases (gamma ? ? ?) #gg #hh @hh
[ elim H #H' #_ @H' normalize >veqb_true @or_introl @refl
| elim H #_ normalize #H' elim H' //
] qed.

lemma gamma_aux4:  
∀(gamma :
  (∀l:list (Variable×Variable)
   .∀c:Crumble
    .(∀x:Variable.rhs l x→inb x c=false)∧distinct_rhs l
     →Σd:Crumble.(∀x:Variable.inb x c=false→¬rhs l x→inb x d=false))).
 ∀(c : Crumble).
 ∀(t : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::t) x→inb x c=false)∧distinct_rhs (〈y,y'〉::t))).
 (∀x:Variable
  .inb x c=false
   →¬rhs (〈y,y'〉::t) x
    →inb x
     (ssc
      (pi1 Crumble
       (λd:Crumble.∀x0:Variable.inb x0 c=false→¬rhs t x0→inb x0 d=false)
       (gamma t c (gamma_aux1 c y y' t H))) y y'
      (gamma_aux3 gamma c t y y' H))
     =false).
#gamma #c #t #y #y' #H #k #Hinc #Hrhs
cut (∀J.  (inb k
  (ssc
   (pi1 Crumble
    (λd:Crumble.∀x0:Variable.inb x0 c=false→¬rhs t x0→inb x0 d=false)
    (gamma t c (gamma_aux1 c y y' t H))) y y' J)
  =false)) [ 2: #UU @UU ] cases gamma #d #h #J
  lapply alpha_fin1 * * * * #Hc #_ #_ #_ #_ @Hc
  [ @h [ @Hinc | % #abs elim Hrhs #Hrhs @Hrhs -Hrhs normalize @or_intror @abs ]
  | lapply Hrhs normalize >veqb_simm cases veqb // * #abs @False_ind @abs
    @or_introl @refl
  ]
qed.

let rec gamma l c on l: (((∀x. rhs l x → inb x c = false) ∧ distinct_rhs l) →
 Σd. ∀x. inb x c = false → ¬rhs l x → inb x d = false) ≝ 
 match l return λl. (((∀x. rhs l x → inb x c = false) ∧ distinct_rhs l) →
 Σd. ∀x. inb x c = false → ¬rhs l x → inb x d = false) with
 [ nil ⇒ λH. «c, gamma_aux2 … H»
 | cons h t ⇒ match h return λh. (((∀x. rhs (h::t) x → inb x c = false) ∧ distinct_rhs (h::t)) →
 Σd. ∀x. inb x c = false → ¬rhs (h::t) x → inb x d = false) with 
  [ mk_Prod y y' ⇒ λH. «(ssc (pi1 Crumble ? (gamma t c (gamma_aux1 … H))) y y' (gamma_aux3 … H)), gamma_aux4 … H» ]
 ] .

definition alpha_c ≝ λc.λn. 
 match c with [CCrumble b e ⇒ λH. alpha b e n H ].
 
lemma alpha_cc_aux1: ∀b, e, y, n.∀ (H : (fresh_var_cc (crc b (envc e y))≤ n)). 
 (fresh_var 〈b,e〉≤ S n).
#b #e #y #n #H
change with (max ? ?≤S n) lapply H
change with (max ? ?) in match (fresh_var_cc ?);
cases y #ny change with (max ? ?) in match (fresh_var_ec ?); #H'
@to_max [ @(le_S … (le_maxl … H')) | @(le_S … (le_maxr … (le_maxr … H'))) ] qed.


lemma alpha_cc_aux2: ∀b, e, n, b1, e1, y.
∀(H : (fresh_var_cc (crc b (envc e y))≤n)).
∀(h':(∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) 〈b1,e1〉=false)).
 (inb_b (νn) b1=false).
#b #e #n #b1 #e1 * #y #H #h'
cut (fresh_var 〈b,e〉≤n∧n<S n)
[ % // change with (max ? ? ≤n) change with ((max ? (max ? ?))≤n) in H;
  @to_max [ @(le_maxl … H) | @(le_maxr … (le_maxr … H)) ] ]
#HH lapply (h' … HH) normalize cases inb_b // >if_t #H @H qed.

lemma alpha_cc_aux3: ∀b, e, n, b1, e1, y.
∀(H : (fresh_var_cc (crc b (envc e y))≤n)).
∀(h':(∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) 〈b1,e1〉=false)).
 (inb_e (νn) e1=false).
#b #e #n #b1 #e1 * #y #H #h'
cut (fresh_var 〈b,e〉≤n∧n<S n)
[ % // change with (max ? ? ≤n) change with ((max ? (max ? ?))≤n) in H;
  @to_max [ @(le_maxl … H) | @(le_maxr … (le_maxr … H)) ] ]
#HH lapply (h' … HH) normalize cases inb_e // >if_monotone #H @H qed.

 
definition alpha_cc: ΠC, n. fresh_var_cc C ≤ n → CrumbleContext  ≝ λC.
 match C return λC. Πn. fresh_var_cc C ≤ n → CrumbleContext with
 [ hole ⇒ λ H.λ_. hole
 | crc b ec ⇒ match ec return λec. Πn. fresh_var_cc (crc b ec) ≤ n → CrumbleContext with
   [ envc e y ⇒λn. λH. match (alpha b e (S n) (alpha_cc_aux1 b e y n H)) with
     [ mk_Sig a h ⇒ match a return λa. (∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) a=false) → CrumbleContext with
       [ CCrumble b1 e1 ⇒ λh'. crc (ssb b1 y (νn) (alpha_cc_aux2 … H h')) (envc (sse e1 y (νn) (alpha_cc_aux3 … H h')) (νn)) ] h
     ]
   ]
 ].
 
lemma gamma_b_aux1: ∀b.∀(H : ((∀x:Variable.rhs [] x→inb_b x b=false)∧distinct_rhs [])).
 (∀x:Variable.inb_b x b=false→¬rhs [] x→inb_b x b=false).
#c #H #k #HH #_ @HH qed.

lemma gamma_b_aux2: ∀b, hd, tl.∀(H : ((∀x:Variable.rhs (hd::tl) x→inb_b x b=false)∧distinct_rhs (hd::tl))).
((∀x:Variable.rhs tl x→inb_b x b=false)∧distinct_rhs tl).
#b #hd #t #H %
  [ #k #HH elim H #HHH #_ @HHH cases hd normalize #y #y' @or_intror @HH
  | elim H #_ cases hd normalize #y #y' * #_ //
  ]
qed.

lemma gamma_b_aux3:  
∀(gamma_b :
  (∀l:list (Variable×Variable)
   .∀b:Bite
    .(∀x:Variable.rhs l x→inb_b x b=false)∧distinct_rhs l
     →Σd:Bite.(∀x:Variable.inb_b x b=false→¬rhs l x→inb_b x d=false))).
 ∀(b : Bite).
 ∀(t : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::t) x→inb_b x b=false)∧distinct_rhs (〈y,y'〉::t))).
 (inb_b y'
  (pi1 Bite (λd:Bite.∀x:Variable.inb_b x b=false→¬rhs t x→inb_b x d=false)
   (gamma_b t b (gamma_b_aux2 b 〈y, y'〉 t H)))
  =false).
#gamma #c #t #y #y' #H cases (gamma ? ? ?) #gg #hh @hh
[ elim H #H' #_ @H' normalize >veqb_true @or_introl @refl
| elim H #_ normalize #H' elim H' //
] qed.

lemma gamma_b_aux4:  ∀(gamma_b :
  (∀b:Bite
   .∀l:list (Variable×Variable)
    .(∀x:Variable.rhs l x→inb_b x b=false)∧distinct_rhs l
     →Σd:Bite.(∀x:Variable.inb_b x b=false→¬rhs l x→inb_b x d=false))).
 ∀(b : Bite).
 ∀(tl : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H :
  ((∀x:Variable.rhs (〈y,y'〉::tl) x→inb_b x b=false)∧distinct_rhs (〈y,y'〉::tl))).
 (∀x:Variable
  .inb_b x b=false
   →¬rhs (〈y,y'〉::tl) x
    →inb_b x
     (ssb
      (pi1 Bite
       (λd:Bite.∀x0:Variable.inb_b x0 b=false→¬rhs tl x0→inb_b x0 d=false)
       (gamma_b b tl (gamma_b_aux2 b 〈y,y'〉 tl H))) y y'
      (gamma_b_aux3 (λl0:list (Variable×Variable).λb0:Bite.gamma_b b0 l0) b tl y
       y' H))
     =false).

#gamma_b #b #tl #y #y' #H #x #Hinb #Hr
cut (∀J.  (inb_b x
  (ssb
   (pi1 Bite (λd:Bite.∀x0:Variable.inb_b x0 b=false→¬rhs tl x0→inb_b x0 d=false)
    (gamma_b b tl (gamma_b_aux2 b 〈y,y'〉 tl H)))
   y y' J)
  =false)) [ 2: #J @J ]
#J cases gamma_b in J ⊢%; #bb #h #J
lapply alpha_fin1 * * * * #_ #Hb #_ #_ #_ @Hb
[ @h [ @Hinb | % #abs elim Hr #Hr' @Hr' normalize @or_intror @abs ]
| elim Hr normalize >veqb_simm cases veqb // #abs @False_ind @abs @or_introl @refl ]
qed.

let rec gamma_b (b:Bite) l on l : ((∀x. rhs l x → inb_b x b = false) ∧ distinct_rhs l) →
 (Σd. ∀x. inb_b x b = false → ¬rhs l x → inb_b x d = false) ≝ 
 match l return λl. ((∀x. rhs l x → inb_b x b = false) ∧ distinct_rhs l) →
 (Σd. ∀x. inb_b x b = false → ¬rhs l x → inb_b x d = false) with
 [ nil ⇒ λH. «b, gamma_b_aux1 b H»
 | cons hd tl ⇒ match hd return λhd. (((∀x. rhs (hd::tl) x → inb_b x b = false) ∧ distinct_rhs (hd::tl)) →
  (Σd. ∀x. inb_b x b = false → ¬rhs (hd::tl) x → inb_b x d = false)) with 
  [ mk_Prod y y' ⇒ λH. «ssb (pi1 Bite ? (gamma_b b tl (gamma_b_aux2 b 〈y, y'〉 tl H))) y y' (gamma_b_aux3 ? b tl y y' H), gamma_b_aux4 … H»  ]
 ] .

lemma gamma_e_aux1: ∀e.∀(H : ((∀x:Variable.rhs [] x→inb_e x e=false)∧distinct_rhs [])).
 (∀x:Variable.inb_e x e=false→¬rhs [] x→inb_e x e=false).
#c #H #k #HH #_ @HH qed.

lemma gamma_e_aux2: ∀e, hd, tl.∀(H : ((∀x:Variable.rhs (hd::tl) x→inb_e x e=false)∧distinct_rhs (hd::tl))).
((∀x:Variable.rhs tl x→inb_e x e=false)∧distinct_rhs tl).
#b #hd #t #H %
  [ #k #HH elim H #HHH #_ @HHH cases hd normalize #y #y' @or_intror @HH
  | elim H #_ cases hd normalize #y #y' * #_ //
  ]
qed.

lemma gamma_e_aux3:  
∀(gamma_e :
  (∀l:list (Variable×Variable)
   .∀e:Environment
    .(∀x:Variable.rhs l x→inb_e x e=false)∧distinct_rhs l
     →Σd:Environment.(∀x:Variable.inb_e x e=false→¬rhs l x→inb_e x d=false))).
 ∀(e : Environment).
 ∀(t : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::t) x→inb_e x e=false)∧distinct_rhs (〈y,y'〉::t))).
 (inb_e y'
  (pi1 Environment ?
   (gamma_e t e (gamma_e_aux2 e 〈y, y'〉 t H)))
  =false).
#gamma #c #t #y #y' #H cases (gamma ? ? ?) #gg #hh @hh
[ elim H #H' #_ @H' normalize >veqb_true @or_introl @refl
| elim H #_ normalize #H' elim H' //
] qed.

lemma gamma_e_aux4:
 ∀(gamma_e :
  (∀e:Environment
   .∀l:list (Variable×Variable)
    .(∀x:Variable.rhs l x→inb_e x e=false)∧distinct_rhs l
     →Σd:Environment.(∀x:Variable.inb_e x e=false→¬rhs l x→inb_e x d=false))).
 ∀(e : Environment).
 ∀(tl : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::tl) x→inb_e x e=false)∧distinct_rhs (〈y,y'〉::tl))). 
  (∀x:Variable
  .inb_e x e=false
   →¬rhs (〈y,y'〉::tl) x
    →inb_e x
     (sse
      (pi1 Environment
       (λd:Environment.∀x0:Variable.inb_e x0 e=false→¬rhs tl x0→inb_e x0 d=false)
       (gamma_e e tl (gamma_e_aux2 e 〈y,y'〉 tl H)))
      y y'
      (gamma_e_aux3 (λl0:list (Variable×Variable).λe0:Environment.gamma_e e0 l0)
       e tl y y' H))
     =false).
     
#gamma_b #b #tl #y #y' #H #x #Hinb #Hr
cut (∀J.   (inb_e x
  (sse
   (pi1 Environment
    (λd:Environment.∀x0:Variable.inb_e x0 b=false→¬rhs tl x0→inb_e x0 d=false)
    (gamma_b b tl (gamma_e_aux2 b 〈y,y'〉 tl H))) y y' J)
  =false)) [ 2: #J @J ]
#J cases gamma_b in J ⊢%; #bb #h #J
lapply alpha_fin1 * * * * #_ #_ #He #_ #_ @He
[ @h [ @Hinb | % #abs elim Hr #Hr' @Hr' normalize @or_intror @abs ]
| elim Hr normalize >veqb_simm cases veqb // #abs @False_ind @abs @or_introl @refl ]
qed.

let rec gamma_e (e:Environment) l on l : ((∀x. rhs l x → inb_e x e = false) ∧ distinct_rhs l) →
 (Σd. ∀x. inb_e x e = false → ¬rhs l x → inb_e x d = false) ≝ 
 match l return λl. ((∀x. rhs l x → inb_e x e = false) ∧ distinct_rhs l) →
 (Σd. ∀x. inb_e x e = false → ¬rhs l x → inb_e x d = false) with
 [ nil ⇒ λH. «e, gamma_e_aux1 e H»
 | cons hd tl ⇒ match hd return λhd. (((∀x. rhs (hd::tl) x → inb_e x e = false) ∧ distinct_rhs (hd::tl)) →
  (Σd. ∀x. inb_e x e = false → ¬rhs (hd::tl) x → inb_e x d = false)) with 
  [ mk_Prod y y' ⇒ λH. «sse (pi1 Environment ? (gamma_e e tl (gamma_e_aux2 e 〈y, y'〉 tl H))) y y' (gamma_e_aux3 ? e tl y y' H), gamma_e_aux4 … H»  ]
 ] .
 
lemma gamma_var_aux1:  ∀y. ∀(H : ((∀x:Variable.rhs [] x→veqb x y=false)∧distinct_rhs [])).
 (∀x:Variable.veqb x y=false→¬rhs [] x→veqb x y=false).
 #c #H #k #HH #_ @HH qed.

lemma gamma_var_aux2:  ∀y, z, z', tl. ∀(H : ((∀x:Variable.rhs (〈z,z'〉::tl) x→veqb x y=false)∧distinct_rhs (〈z,z'〉::tl))).
 ((∀x:Variable.rhs tl x→veqb x y=false)∧distinct_rhs tl).
#b #z #z' #t #H %
  [ #k #HH elim H #HHH #_ @HHH normalize @or_intror @HH
  | elim H #_ normalize * #_ //
  ]
qed.
lemma gamma_var_aux4:
 ∀(gamma_var :
  (∀y:Variable
   .∀l:list (Variable×Variable)
    .(∀x:Variable.rhs l x→veqb x y=false)∧distinct_rhs l
     →Σd:Variable.(∀x:Variable.veqb x y=false→¬rhs l x→veqb x d=false))).
 ∀y.∀tl.∀z.∀z'.
 ∀(H : ((∀x:Variable.rhs (〈z,z'〉::tl) x→veqb x y=false)∧distinct_rhs (〈z,z'〉::tl))).
 (∀x:Variable
  .veqb x y=false
   →¬rhs (〈z,z'〉::tl) x
    →veqb x
     (if veqb
           (pi1 Variable
            (λd:Variable.∀x0:Variable.veqb x0 y=false→¬rhs tl x0→veqb x0 d=false)
            (gamma_var y tl (gamma_var_aux2 y z z' tl H))) z 
      then z' 
      else pi1 Variable
               (λd:Variable.∀x0:Variable.veqb x0 y=false→¬rhs tl x0→veqb x0 d=false)
               (gamma_var y tl (gamma_var_aux2 y z z' tl H)) )
     =false).
#gamma_var #y #tl #z #z' #H
cases gamma_var #w #hh #k #H1 #H2
cut (veqb w z = true ∨ veqb w z = false) // * #Hwz >Hwz normalize
[ 2: @hh // % #abs elim H2 #H2' @H2' normalize @or_intror @abs
| elim (veqb_true_to_eq w z) #Heq #_ lapply (Heq Hwz) -Heq #Heq destruct
  lapply H2 normalize cases veqb // * #abs @False_ind @abs @or_introl @refl
] qed.

let rec gamma_var (y:Variable) (l: list (Variable×Variable)) on l:
((∀x. rhs l x → veqb x y = false) ∧ distinct_rhs l) →
 (Σd. ∀x. veqb x y = false → ¬rhs l x → veqb x d = false) ≝ 
 match l return λl. ((∀x. rhs l x → veqb x y = false) ∧ distinct_rhs l) →
 (Σd. ∀x. veqb x y = false → ¬rhs l x → veqb x d = false) with
 [ nil ⇒ λH. «y, gamma_var_aux1 y H»
 | cons hd tl ⇒ match hd return λhd. ((∀x. rhs (hd::tl) x → veqb x y = false) ∧ distinct_rhs (hd::tl)) →
 (Σd. ∀x. veqb x y = false → ¬rhs (hd::tl) x → veqb x d = false) with 
  [ mk_Prod z z' ⇒ λH. «match veqb (pi1 Variable ? (gamma_var y tl (gamma_var_aux2 … H))) z with
    [ true ⇒ z' 
    | false ⇒ (pi1 Variable ? (gamma_var y tl (gamma_var_aux2 … H)))
    ] , gamma_var_aux4 … H »  ]
 ] .
 
lemma gamma_ec_aux1: ∀l, e, y.
 ∀(H : ((∀x:Variable.rhs l x→inb_ec x (envc e y)=false)∧distinct_rhs l)).  
 ((∀x:Variable.rhs l x→inb_e x e=false)∧distinct_rhs l).
#l #e #y #H elim H -H #Ha #Hb % // #k #HH lapply (Ha k HH) normalize cases inb_e //
  >if_monotone #H @H qed.

lemma gamma_ec_aux2: ∀l, e, y.
 ∀(H : ((∀x:Variable.rhs l x→inb_ec x (envc e y)=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→veqb x y=false)∧distinct_rhs l).
#l #e #y #H elim H -H #Ha #Hb % // #k #HH lapply (Ha k HH) normalize cases veqb //
  >if_t #H @H qed.

definition gamma_ec ≝ λec.λl.
 match ec return λec. ((∀x. rhs l x → inb_ec x ec = false) ∧ distinct_rhs l) → EnvContext with
 [ envc e y ⇒ λH. envc (pi1 … (gamma_e e l (gamma_ec_aux1 … H))) (pi1 … (gamma_var y l (gamma_ec_aux2 … H))) ].

lemma gamma_cc_aux1: ∀l, b, ec. ∀(H : ((∀x:Variable.rhs l x→inb_cc x (crc b ec)=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→inb_b x b=false)∧distinct_rhs l).
#l #b #ec * #Ha #Hb % // #k #HH lapply (Ha k HH) whd in match (inb_cc ? ?); cases inb_b //
  >if_t #H @H qed.
  
lemma gamma_cc_aux2: ∀l, b, ec. ∀(H : ((∀x:Variable.rhs l x→inb_cc x (crc b ec)=false)∧distinct_rhs l)).
((∀x:Variable.rhs l x→inb_ec x ec=false)∧distinct_rhs l).
#l #b #ec * #Ha #Hb % // #k #HH lapply (Ha k HH) whd in match (inb_cc ? ?); cases inb_ec //
  >if_monotone #H @H qed.

definition gamma_cc ≝ λC.λl.
 match C return λC. ((∀x. rhs l x → inb_cc x C = false) ∧ distinct_rhs l) → CrumbleContext with
 [ hole ⇒ λ_. hole
 | crc b ec ⇒ λH. crc (pi1 … (gamma_b b l (gamma_cc_aux1 l b ec H))) ((gamma_ec ec l (gamma_cc_aux2 l b ec H)))
 ].

lemma fresh_var_over_plug: ∀C,c. fresh_var (plug_c C c) = max (fresh_var_cc C) (fresh_var c).
* [ #c normalize cases c #b #e whd in match (plug_c hole ?); @refl ]
#b * #e * #y * #bb #ee whd in match (plug_c ? ?); whd in match (plug_e ? ?);
change with (max ? ?) in match (fresh_var_cc ?);
change with (max ? ?) in match (fresh_var ?);
>fresh_var_concat change with (max ? ?) in match (fresh_var ?);
change with (max ? ?) in match (fresh_var_e ?);
change with (max (S ?) ?) in match (fresh_var_s ?);
change with (max ? ?) in match (fresh_var_ec ?); /2/ qed.

definition e_len_c ≝ λc.
 match c with
 [CCrumble b e ⇒ e_len e].


lemma in_alpha: ∀c, x, n, H. fresh_var c ≤ x → x < n → inb (νx) (pi1 … (alpha_c c n H)) = false.
* #b @Environment_simple_ind2
[ #x #n #H #H1 #H2 normalize >if_then_true_else_false
  change with (max ? 0 ≤x) in H1; lapply (le_maxl … H1)
  lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb
| #e * * #y #b' #HI #x #n #H #H1 #H2
  change with (alpha ? ? ? ?) in match (alpha_c ? ? ?);
  change with (match alpha b ? (S n) ? with
     [ mk_Sig a h ⇒ mk_Sig …(at (ssc (a) (νy) (νn) ?) (Snoc Epsilon (subst ? ?))) ? ]) in match (alpha ? ? ? ?);
     
  lapply (HI x (S n) (alpha_aux1 b e [νy←b'] n H) ? (le_S … H2))
  [ change with (max ? (max ? ?)≤?) in H1; @to_max [ @(le_maxl … H1) | @(le_maxl … (le_maxr … H1)) ] ]
  whd in match (alpha_c ? ? ?); cases alpha #a #h -HI #HI
  change with (inb (νx) (at (ssc a (νy) (νn) ?) (Snoc Epsilon [νn←b']))=false)
  @alpha_aux4 [4: @H | skip | skip | @h | % // ]
] qed.

 
lemma in_alpha_cc: ∀C, x, n, H. fresh_var_cc C ≤ x → x < n → inb_cc (νx) (alpha_cc C n H) = false.
* [ #x #n #H normalize // ]
#b * #e * #y #x #n #H change with (max ? (max (S ?) ?)) in match (fresh_var_cc ?); 
#H1 #H2 change with (match (alpha b e (S n) ?) with
     [ mk_Sig a h ⇒ match a return λa. (∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) a=false) → CrumbleContext with
       [ CCrumble b1 e1 ⇒ λh'. crc (ssb b1 (νy) (νn) ?) (envc (sse e1 (νy) (νn) ?) ?) ] h
     ] ) in match (alpha_cc ? ? ?);
letin KK ≝ (alpha_cc_aux1 b e (νy) n H)
cut (∀KK.  (inb_cc (νx)
  match alpha b e (S n) KK
   in Sig
   return 
  λ_:(Σc:Crumble.(∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) c=false)).CrumbleContext
   with 
  [mk_Sig (a:Crumble)   (h:(∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) a=false))⇒
   match a
    in Crumble
    return 
   λa0:Crumble.((∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) a0=false)→CrumbleContext)
    with 
   [CCrumble (b1:Bite)   (e1:Environment)⇒
    λh':∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S n→inb (νm) 〈b1,e1〉=false
    .crc (ssb b1 (νy) (νn) (alpha_cc_aux2 b e n b1 e1 (νy) H h'))
     (envc (sse e1 (νy) (νn) (alpha_cc_aux3 b e n b1 e1 (νy) H h')) νn)] h]
  =false)) [ 2: #UU @UU ]
#KK lapply (in_alpha (CCrumble b e) x (S n) KK ? (le_S … H2))
 [ change with (max ? ?≤?) @to_max [ @(le_maxl … H1) | @(le_maxr … (le_maxr … H1)) ] ]
whd in match (alpha_c ? ? ?); cases alpha * #ab #ae #h #Ha

change with ((inb_cc (νx) (crc (ssb ab (νy) (νn) (alpha_cc_aux2 b e n ab ae (νy) H ?))
     (envc (sse ae (νy) (νn) (alpha_cc_aux3 b e n ab ae (νy) H ?)) νn))= false))
whd in match (inb_cc ? ?);
whd in match (inb_ec ? ?);
whd in match (veqb ? ?);
cut (neqb x n = true ∨ neqb x n = false) // * #Hxn >Hxn [ >if_t 
elim (neqb_iff_eq x n) #Heq #_ lapply (Heq Hxn) -Heq #Heq destruct
@False_ind lapply (H2) @le_Sn_n ] >if_f
lapply alpha_fin1 * * * * #_ #Hb #He #_ #_ >Hb //
[ 2: lapply (h x ?) [ % 
  [ change with (max ? ?≤?) @to_max [ @(le_maxl … H1) | @(le_maxr … (le_maxr … H1)) ] ]
  @(le_S … H2) ]
  normalize cases inb_b // >if_t #H @H
] >He // lapply (h x ?) [ % 
  [ change with (max ? ?≤?) @to_max [ @(le_maxl … H1) | @(le_maxr … (le_maxr … H1)) ] ]
  @(le_S … H2) ]
  normalize cases inb_e // >if_monotone #H @H
 
qed.

lemma betae_rhs_bound: ∀e, n, x. rhs (beta_e e n) (νx) → n ≤ x ∧ x < n+ e_len e.
@Environment_simple_ind2
[ #n #x normalize #abs @False_ind @abs
| #e * * #y #b #HI #n #x whd in match (beta ? ?); whd in match (rhs ? ?); *
  [ whd in match (veqb ? ?); #HH elim (neqb_iff_eq x n) #Heq #_
    lapply (Heq HH) -Heq #Heq destruct % // whd in match (e_len_c ?);
    normalize //
  | #H lapply (HI … H) * #Ha #Hb %
    [ cut (n ≤ S n) [ // ] #Htmp @(transitive_le … Htmp Ha)
    | lapply Hb normalize <plus_n_Sm #Hb @Hb 
    ]
  ]
] qed.

lemma beta_rhs_bound: ∀c, n, x. rhs (beta c n) (νx) → n ≤ x ∧ x < n+ e_len_c c.
* #b #e #n #x whd in match (beta ? ?); whd in match (e_len_c ?);
@betae_rhs_bound qed.

lemma gamma_lemma_aux1: ∀c, D, n. ∀(H : (fresh_var (plug_c D c)≤n)). (fresh_var c≤n).
#c #d normalize >fresh_var_over_plug #H' @(le_maxr … H') qed.

lemma gamma_lemma_aux2: ∀c, D, n. ∀(H : (fresh_var (plug_c D c)≤n)). (fresh_var_cc D≤n+e_len_c c).
#c #D #n >fresh_var_over_plug #H' lapply (le_maxl … H') -H' #H' @le_plus_a_r @H' qed.

lemma gamma_lemma_aux3: ∀c, D, n. ∀(H : (fresh_var (plug_c D c)≤n)). ∀K.  
 ((∀x:Variable
   .rhs (beta c n) x
    →inb_cc x (alpha_cc D (n+e_len_c c) K)=false)
  ∧distinct_rhs (beta c n)).

#c #D #n #H #K % [ 2: @distinct_rhs_beta ] * #x #HH @in_alpha_cc
[ lapply (beta_rhs_bound … HH) * #Ha #Hb >fresh_var_over_plug in H; #H
  @(transitive_le … (le_maxl … H) Ha)
| lapply (beta_rhs_bound … HH) * #Ha #Hb @Hb
] qed.

lemma plug_hole: ∀c. plug_c hole c = c.  * #b #e // qed.

lemma diletta: ∀x. x - 1 ≤ x.
#x cases x
[ normalize @le_n
| #n //
] qed.

lemma diletta2: ∀x. (x - 1) - 1 ≤ x.
#x lapply (diletta x) #H1 lapply (diletta (x-1)) #H2
@(transitive_le … H2 H1) qed.

lemma gamma_technical_lemma: ∀b,e,x,y,H,H'. neqb x y= true →  pi1 … (alpha b e (x) H) = pi1 … (alpha b e y H').
#b @Environment_simple_ind2
[ #n #H #H' normalize //
| #e * #y #B #HI #x #z #H #H' #HH
  whd in match (alpha ? ? ? ?);
  whd in match (alpha ? ? z ?);
  lapply (HI (S x) (S z) ? ? ?)
  [ normalize @HH
  | @(alpha_aux1 … [y←B]) @H'
  | @(alpha_aux1 … [y←B]) @H
  ]
  cases alpha #a #h cases alpha #c #j #Heq destruct 
  whd in match (match ? in Sig with [_⇒?]);
  whd in match (match ? in Sig with [_⇒?]);
  elim (neqb_iff_eq x z) #Heq #_ lapply (Heq HH) -Heq #Heq destruct //
] qed.


lemma gamma_b_no_subst: ∀b, H. pi1 … (gamma_b b [] H) = b.
#b #H // qed.

lemma gamma_e_no_subst: ∀e, H. pi1 … (gamma_e e [] H) = e.
#b #H // qed.

lemma gamma_var_no_subst: ∀y, H. pi1 … (gamma_var y [] H) = y.
#b #H // qed.

lemma gamma_technical_lemma2: ∀b, e, y, B, ee, s, n.
∀(H :(fresh_var 〈b,Snoc (concat (Snoc e [y←B]) ee) s〉≤n)).  
 (fresh_var (plug_c (crc b (envc e y)) 〈B,ee〉)≤S n).
#b #e #y #B #ee #s #n #H
>fresh_var_over_plug lapply H
  change with (max ? ?) in match (fresh_var ?);
  change with (max ? ?) in match (fresh_var_e ?);  >fresh_var_concat
  change with (max ? ?) in match (fresh_var_e ?); cases y #ny
  change with (max (S ?) ?) in match (fresh_var_s ?); -H #H
  change with (max (max ? (max ? ?))(max ? ?)≤S n) @to_max
  [ @to_max 
    [ @(le_S … (le_maxl … H))
    | @to_max
      [ @(le_S …(le_maxl …( le_maxr … (le_maxl … (le_maxl … (le_maxr … H))))))
      | @(le_S …( le_maxl … (le_maxl … (le_maxl … (le_maxr … H)))))
      ]
    ]
  | @to_max
    [ @(le_S …(le_maxr …( le_maxr … (le_maxl … (le_maxl … (le_maxr … H))))))
    | @(le_S … (le_maxr … (le_maxl … (le_maxr … H))))
    ]
  ]
qed.

lemma veqb_to_ssb: ∀b, y, z, z', H, H'. veqb z z' = true → 
 (ssb b y z H) = (ssb b y z' H').
#b #y #z #z' #H #H' #HH elim (veqb_true_to_eq … z z') #Heq #_ lapply (Heq HH)
-Heq #Heq destruct // qed.

lemma sse_concat_aux1: ∀x, e, f. inb_e x (concat e f) = false → inb_e x e = false.
#x #e #f >inb_concat #H lapply (orb_false … H) * // qed.  

lemma sse_concat_aux2: ∀x, e, f. inb_e x (concat e f) = false → inb_e x f = false.
#x #e #f >inb_concat #H lapply (orb_false … H) * // qed.  


lemma sse_concat: ∀f, e, y, y', H. sse (concat e f) y y' H = 
concat (sse e y y' (sse_concat_aux1 … H)) (sse f y y' (sse_concat_aux2 … H)).
@Environment_simple_ind2
[ #e #y #y' #H //
| #f * #z #b #HI #e #y #y' #H whd in match (concat ??);
 whd in match (sse ? ? ? ?);
 whd in match (sse (Snoc ? ?) ? ? ?);
 cases (veqb)
 [ >if_t >if_t
   whd in ⊢ (? ? ? (? ? %));
   whd in ⊢ (? ? (%) ?);
   whd in match (concat ? (Snoc ? ?));
   @eq_f2
   [ >HI //
   | @eq_f2 //
   ]
 | >if_f >if_f
   whd in ⊢ (? ? ? (? ? %));
   whd in ⊢ (? ? (%) ?);
   whd in match (concat ? (Snoc ? ?));
   @eq_f2
   [ >HI //
   | @eq_f2 //
   ]
 ]
] qed.

lemma gamma_lemma: ∀D, c, n, H. (pi1 … (alpha_c (plug_c D c) n H)) = plug_c (gamma_cc (alpha_cc D (n+e_len_c c) (gamma_lemma_aux2 c D n H) ) (beta c n) (gamma_lemma_aux3 c D n H (gamma_lemma_aux2 c D n H))) (pi1 … (alpha_c c n (gamma_lemma_aux1 c D n H))).
*
[ * #b #e #n whd in match (plug_c hole ?); whd in match (alpha_cc hole ? ?);
  [ 3: @le_n | 2: skip ]
  whd in match (plug_c hole ?); #H whd in match (alpha_c ? ? ?); >plug_hole // ]
#b * #e #y * #B @Environment_simple_ind2
[ #n whd in match (plug_c ? ?); whd in match (plug_e ? ?); #H
whd in match (alpha_c ? ? ?); whd in match (alpha_c ? ? ?);
whd in match (alpha_cc ? ? ?); whd in match (e_len_c ? );
whd in match (beta ? ?); whd in match (gamma_cc ? ? ?);

lapply (gamma_technical_lemma b e (S n) (S (n+0)) (alpha_aux1 b e [y←B] n H)
     (alpha_cc_aux1 b e y (n+O) (gamma_lemma_aux2 〈B,Epsilon〉 (crc b (envc e y)) n H)) ?)
[ // ]

cases alpha #a #h 
change with (at (ssc a y (νn) (alpha_aux3 b e a n y B h H)) (Snoc Epsilon [νn←B])) in ⊢ (? → (? ? % ?));
letin K ≝ (alpha_cc_aux1 b e y (n+O) (gamma_lemma_aux2 〈B,Epsilon〉 (crc b (envc e y)) n H))
letin J ≝ (gamma_lemma_aux3 〈B,Epsilon〉 (crc b (envc e y)) n H
     (gamma_lemma_aux2 〈B,Epsilon〉 (crc b (envc e y)) n H))
letin L ≝ (alpha_aux3 b e a n y B h H)
cut (∀K, J, L.
 (a=pi1 Crumble ? (alpha b e (S (n+O)) K)
  →(at (ssc a y (νn) L)(Snoc Epsilon [νn←B]))
   =plug_c
    (match 
     match alpha b e (S (n+O)) K in Sig 
      with 
     [mk_Sig
      (a0:Crumble) h0⇒
      match a0
       in Crumble
       with 
      [CCrumble b1 e1⇒
       λh':∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (n+O)→inb (νm) 〈b1,e1〉=false
       .crc
        (ssb b1 y (ν(n+O))
         (alpha_cc_aux2 b e (n+O) b1 e1 y
          (gamma_lemma_aux2 〈B,Epsilon〉 (crc b (envc e y)) n H) h'))
        (envc
         (sse e1 y (ν(n+O))
          (alpha_cc_aux3 b e (n+O) b1 e1 y
           (gamma_lemma_aux2 〈B,Epsilon〉 (crc b (envc e y)) n H) h')) (ν(n+O)))] h0]
      in CrumbleContext
      return 
     λC0:CrumbleContext
     .((∀x:Variable.rhs [] x→inb_cc x C0=false)∧distinct_rhs []→CrumbleContext)
      with 
     [hole⇒λ_:(∀x:Variable.rhs [] x→inb_cc x hole=false)∧distinct_rhs [].hole
     |crc (b0:Bite)   (ec:EnvContext)⇒
      λH0:(∀x:Variable.rhs [] x→inb_cc x (crc b0 ec)=false)∧distinct_rhs []
      .crc
       (pi1 Bite
        (λd:Bite.∀x:Variable.inb_b x b0=false→¬rhs [] x→inb_b x d=false)
        (gamma_b b0 [] (gamma_cc_aux1 [] b0 ec H0)))
       (gamma_ec ec [] (gamma_cc_aux2 [] b0 ec H0))]
     J)
    〈B,Epsilon〉)) [ 2: #UU @UU ]
 #K #J #L
#HHH lapply HHH lapply L lapply J lapply K lapply h 
cases     ( (alpha b e (S (n+O)) K)) * #BB #EE #hh

whd in match (match ? in Sig with [_⇒?]);
-h #h -K #K #J -L #L #HHH destruct
>gamma_b_no_subst
whd in match (gamma_ec ? ? ?);
>gamma_e_no_subst
>gamma_var_no_subst
cut (∀FF, GG.  (at (ssc 〈BB,EE〉 y (νn) L) (Snoc Epsilon [νn←B])
  =plug_c
   (crc
    (ssb BB y (ν(n+O)) FF)
    (envc
     (sse EE y (ν(n+O)) GG) ν(n+O))) 〈B,Epsilon〉))
[ 2: #UU @UU ] #FF #GG normalize @eq_f2
[ cut (n+0 =n) // #HH >HH in FF GG ⊢ %; //
| @eq_f2 // cut (n+0 =n) // #HH >HH in FF GG ⊢ %; #HHA #HHB @refl
]
| #ee * #z #bb #HI #n whd in match (plug_c ? ?);  whd in match (plug_e ? ?); #H
whd in match (alpha_c ? ? ?); whd in match (alpha_c ? ? ?);
whd in match (alpha_cc ? ? ?); whd in match (e_len_c ? );
whd in match (beta ? ?); whd in match (gamma_cc ? ? ?);
lapply (HI (S n) (gamma_technical_lemma2 … H)) 
whd in match (plug_c ? ?);  whd in match (plug_e ? ?);
whd in match (alpha_c ? ? ?); whd in match (alpha_c ? ? ?);
whd in match (alpha_cc ? ? ?); whd in match (e_len_c ? );
cases   (alpha b (concat (Snoc e [y←B]) ee) (S n)
   (gamma_technical_lemma2 b e y B ee [z←bb] n H))
#a #h
whd in match (match «a,h»
    in Sig
    with 
   [mk_Sig
    (a0:Crumble)
     
    h0⇒
    «at (ssc a0 z (νn) (alpha_aux3 b (concat (Snoc e [y←B]) ee) a0 n z bb h0 H))(Snoc Epsilon [νn←bb]),
    alpha_aux4 b (concat (Snoc e [y←B]) ee) a0 n z bb
    (alpha_aux3 b (concat (Snoc e [y←B]) ee) a0 n z bb h0 H) h0 H»]);
 cases (alpha B ee (S n)        (alpha_aux1 B ee [z←bb] n
        (gamma_lemma_aux1 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H))) * #aab #aae #hh
        
whd in match (match «CCrumble aab aae,hh»
      in Sig
      with 
     [mk_Sig (a0:Crumble) h0
      ⇒
      «at (ssc a0 z (νn) ?) (Snoc Epsilon [νn←bb]),
      alpha_aux4 B ee a0 n z bb
      (alpha_aux3 B ee a0 n z bb h0
       (gamma_lemma_aux1 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H)) h0
      (gamma_lemma_aux1 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H)»]);

lapply (gamma_technical_lemma b e (S (S n+ e_len ee)) (S (n+(S (e_len ee)))) (alpha_cc_aux1 b e y (S n+e_len ee)
     (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
      (gamma_technical_lemma2 b e y B ee [z←bb] n H)))
      (alpha_cc_aux1 b e y (n+S (e_len ee))
      (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H)) ?) [ <plus_n_Sm // ]
(*
letin P1 ≝ (alpha_cc_aux1 b e y (S n+e_len ee)
    (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
     (gamma_technical_lemma2 b e y B ee [z←bb] n H)))
letin P2 ≝ ((alpha_cc_aux1 b e y (n+S (e_len ee))
     (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H)))
letin P3 ≝ (gamma_lemma_aux3 〈B,ee〉 (crc b (envc e y)) (S n)
      (gamma_technical_lemma2 b e y B ee [z←bb] n H)
      (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
       (gamma_technical_lemma2 b e y B ee [z←bb] n H)))
letin P4 ≝ (gamma_lemma_aux3 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H
       (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H))
letin P5 ≝ (alpha_aux3 B ee 〈aab,aae〉 n z bb hh
       (gamma_lemma_aux1 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H))
letin P6 ≝ (alpha_aux3 b (concat (Snoc e [y←B]) ee) a n z bb h H)
*)
cut (∀P1, P2, P3, P4, P5, P6.   (pi1 Crumble ? (alpha b e (S (S n+e_len ee)) P1)
  =pi1 Crumble ? (alpha b e (S (n+S (e_len ee))) P2)
  →a
   =plug_c
    (gamma_cc
     match alpha b e (S (S n+e_len ee)) P1
      in Sig
(*      return 
     λ_0:(Σc:Crumble.(∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (S n+e_len ee)→inb νm c=false)) 
     .CrumbleContext *)
      with 
     [mk_Sig a0 h0⇒
      match a0
       in Crumble
(*       return 
      λa00:Crumble
      .((∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (S n+e_len ee)→inb νm a00=false)
        →CrumbleContext) *)
       with 
      [CCrumble (b1:Bite)   (e1:Environment)⇒
       λh':∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (S n+e_len ee)→inb (νm) 〈b1,e1〉=false
       .crc
        (ssb b1 y (ν(S n+e_len ee))
         (alpha_cc_aux2 b e (S n+e_len ee) b1 e1 y
          (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
           (gamma_technical_lemma2 b e y B ee [z←bb] n H)) h'))
        (envc
         (sse e1 y (ν(S n+e_len ee))
          (alpha_cc_aux3 b e (S n+e_len ee) b1 e1 y
           (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
            (gamma_technical_lemma2 b e y B ee [z←bb] n H)) h')) (ν(S n+e_len ee)))]
      h0]
     (beta 〈B,ee〉 (S n)) P3)
    〈aab,aae〉
   →(at (ssc a z (νn) P6) (Snoc Epsilon [νn←bb]))
    =plug_c
     (match 
      match alpha b e (S (n+S (e_len ee))) P2
       in Sig
(*       return 
      λ_0:(Σc:Crumble
               .(∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (n+S (e_len ee))→inb νm c=false))
      .CrumbleContext *)
       with 
      [mk_Sig a0 h0⇒
       match a0
        in Crumble
(*        return 
       λa00:Crumble
       .((∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (n+S (e_len ee))→inb νm a00=false)
         →CrumbleContext) *)
        with 
       [CCrumble (b1:Bite)   (e1:Environment)⇒
        λh':∀m:ℕ.fresh_var 〈b,e〉≤m∧m<S (n+S (e_len ee))→inb (νm) 〈b1,e1〉=false
        .crc
         (ssb b1 y (ν(n+S (e_len ee)))
          (alpha_cc_aux2 b e (n+S (e_len ee)) b1 e1 y
           (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H) h'))
         (envc
          (sse e1 y (ν(n+S (e_len ee)))
           (alpha_cc_aux3 b e (n+S (e_len ee)) b1 e1 y
            (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H) h'))
          (ν(n+S (e_len ee))))] h0]
       in CrumbleContext
       return 
      λC0:CrumbleContext
      .((∀x:Variable.rhs (〈z,νn〉::beta_e ee (S n)) x→inb_cc x C0=false)
        ∧distinct_rhs (〈z,νn〉::beta_e ee (S n))
        →CrumbleContext)
       with 
      [hole⇒
       λ_:(∀x:Variable.rhs (〈z,νn〉::beta_e ee (S n)) x→inb_cc x hole=false)
               ∧distinct_rhs (〈z,νn〉::beta_e ee (S n))
       .hole
      |crc (b0:Bite)   (ec:EnvContext)⇒
       λH0:(∀x:Variable
                .rhs (〈z,νn〉::beta_e ee (S n)) x→inb_cc x (crc b0 ec)=false)
               ∧distinct_rhs (〈z,νn〉::beta_e ee (S n))
       .crc
        (pi1 Bite
         (λd:Bite
          .∀x:Variable
           .inb_b x b0=false→¬rhs (〈z,νn〉::beta_e ee (S n)) x→inb_b x d=false)
         (gamma_b b0 (〈z,νn〉::beta_e ee (S n))
          (gamma_cc_aux1 (〈z,νn〉::beta_e ee (S n)) b0 ec H0)))
        (gamma_ec ec (〈z,νn〉::beta_e ee (S n))
         (gamma_cc_aux2 (〈z,νn〉::beta_e ee (S n)) b0 ec H0))] P4)
     ((at (ssc 〈aab,aae〉 z (νn) P5) (Snoc Epsilon [νn←bb])))) ) [2: #UUU @UUU ]
#P1
cases (alpha b e (S (S n+e_len ee)) ?) *
#aAb #aAe #hH #P2
cases (alpha b e (S (n+S (e_len ee))) P2) *
#Aab #Aae #Hh #P3 #P4 #P5 #P6

whd in match (match ? in Sig with [_⇒?]);
whd in match (match ? in Sig with [_⇒?]);
whd in match (match ? in CrumbleContext with [_⇒ ?]);
#Heq destruct
whd in ⊢ (? → (? ? ? (? % ?))); -P1 -P2
(*
letin P1 ≝ (alpha_cc_aux2 b e (S n+e_len ee) Aab Aae y
       (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
        (gamma_technical_lemma2 b e y B ee [z←bb] n H)) hH)
letin P2 ≝ (alpha_cc_aux3 b e (S n+e_len ee) Aab Aae y
        (gamma_lemma_aux2 〈B,ee〉 (crc b (envc e y)) (S n)
         (gamma_technical_lemma2 b e y B ee [z←bb] n H)) hH)
letin P7 ≝ (alpha_cc_aux2 b e (n+S (e_len ee)) Aab Aae y
           (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H) Hh)
letin P8 ≝ (gamma_cc_aux1 (〈z,νn〉::beta_e ee (S n)) (ssb Aab y (ν(n+S (e_len ee))) P7)
        (envc
         (sse Aae y (ν(n+S (e_len ee)))
          (alpha_cc_aux3 b e (n+S (e_len ee)) Aab Aae y
           (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H) Hh))
         (ν(n+S (e_len ee)))) P4)
letin P9 ≝ (alpha_cc_aux3 b e (n+S (e_len ee)) Aab Aae y
         (gamma_lemma_aux2 〈B,Snoc ee [z←bb]〉 (crc b (envc e y)) n H) Hh)
letin P10 ≝ (gamma_cc_aux2 (〈z,νn〉::beta_e ee (S n)) (ssb Aab y (ν(n+S (e_len ee))) P7)
       (envc (sse Aae y (ν(n+S (e_len ee))) P9) (ν(n+S (e_len ee)))) P4)
*)
     
cut (∀P1, P2, P7, P8, P9, P10.  (a
  =plug_c
   (gamma_cc
    (crc (ssb Aab y (ν(S n+e_len ee)) P1)
     (envc (sse Aae y (ν(S n+e_len ee)) P2) (ν(S n+e_len ee)))) (beta 〈B,ee〉 (S n))
    P3)
   〈aab,aae〉
  →(at (ssc a z (νn) P6) (Snoc Epsilon [νn←bb]))
   =plug_c
    (crc
     (pi1 Bite
      (λd:Bite
       .∀x:Variable
        .inb_b x (ssb Aab y (ν(n+S (e_len ee))) P7)=false
         →¬rhs (〈z,νn〉::beta_e ee (S n)) x→inb_b x d=false)
      (gamma_b (ssb Aab y (ν(n+S (e_len ee))) P7) (〈z,νn〉::beta_e ee (S n)) P8))
     (gamma_ec (envc (sse Aae y (ν(n+S (e_len ee))) P9) (ν(n+S (e_len ee))))
      (〈z,νn〉::beta_e ee (S n)) P10))
    (at (ssc 〈aab,aae〉 z (νn) P5)(Snoc Epsilon [νn←bb])))) [ 2: #uu @uu ]
#P1 #P2 #P7 #P8 #P9 #P10 -P4
whd in match (gamma_cc ? ? ?);
(*
letin P4 ≝ (gamma_cc_aux1 (beta 〈B,ee〉 (S n)) (ssb Aab y (ν(S n+e_len ee)) P1)
       (envc (sse Aae y (ν(S n+e_len ee)) P2) (ν(S n+e_len ee))) P3)
letin P11 ≝ (gamma_cc_aux2 (beta 〈B,ee〉 (S n)) (ssb Aab y (ν(S n+e_len ee)) P1)
      (envc (sse Aae y (ν(S n+e_len ee)) P2) (ν(S n+e_len ee))) P3)
*)
cut (∀P4, P11.  (a
  =plug_c
   (crc
    (pi1 Bite
     (λd:Bite
      .∀x:Variable
       .inb_b x (ssb Aab y (ν(S n+e_len ee)) P1)=false
        →¬rhs (beta 〈B,ee〉 (S n)) x→inb_b x d=false)
     (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta 〈B,ee〉 (S n)) P4))
    (gamma_ec (envc (sse Aae y (ν(S n+e_len ee)) P2) (ν(S n+e_len ee)))
     (beta 〈B,ee〉 (S n)) P11)) 〈aab,aae〉
  →(at (ssc a z (νn) P6)(Snoc Epsilon [νn←bb]))
   =plug_c
    (crc
     (pi1 Bite
      (λd:Bite
       .∀x:Variable
        .inb_b x (ssb Aab y (ν(n+S (e_len ee))) P7)=false
         →¬rhs (〈z,νn〉::beta_e ee (S n)) x→inb_b x d=false)
      (gamma_b (ssb Aab y (ν(n+S (e_len ee))) P7) (〈z,νn〉::beta_e ee (S n)) P8))
     (gamma_ec (envc (sse Aae y (ν(n+S (e_len ee))) P9) (ν(n+S (e_len ee))))
      (〈z,νn〉::beta_e ee (S n)) P10))
    (at (ssc 〈aab,aae〉 z (νn) P5) (Snoc Epsilon [νn←bb]))) )
[ 2: #uu @uu ] #P4 #P11

whd in match (gamma_ec ? ? ?);
whd in match (gamma_ec ? ? ?);
(*
letin P12 ≝ (gamma_ec_aux1 (beta 〈B,ee〉 (S n)) (sse Aae y (ν(S n+e_len ee)) P2)
        (ν(S n+e_len ee)) P11)
letin P13 ≝ (gamma_ec_aux2 (beta 〈B,ee〉 (S n)) (sse Aae y (ν(S n+e_len ee)) P2)
        (ν(S n+e_len ee)) P11)
letin P14 ≝ (gamma_ec_aux1 (〈z,νn〉::beta_e ee (S n))
         (sse Aae y (ν(n+S (e_len ee))) P9) (ν(n+S (e_len ee))) P10)
letin P15 ≝ (gamma_ec_aux2 (〈z,νn〉::beta_e ee (S n))
         (sse Aae y (ν(n+S (e_len ee))) P9) (ν(n+S (e_len ee))) P10)
*)       
cut (∀ P12, P13, P14, P15.   (a
  =plug_c
   (crc
    (pi1 Bite
     (λd:Bite
      .∀x:Variable
       .inb_b x (ssb Aab y (ν(S n+e_len ee)) P1)=false
        →¬rhs (beta 〈B,ee〉 (S n)) x→inb_b x d=false)
     (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta 〈B,ee〉 (S n)) P4))
    (envc
     (pi1 Environment
      (λd:Environment
       .∀x:Variable
        .inb_e x (sse Aae y (ν(S n+e_len ee)) P2)=false
         →¬rhs (beta 〈B,ee〉 (S n)) x→inb_e x d=false)
      (gamma_e (sse Aae y (ν(S n+e_len ee)) P2) (beta 〈B,ee〉 (S n)) P12))
     (pi1 Variable
      (λd:Variable
       .∀x:Variable
        .veqb x (ν(S n+e_len ee))=false→¬rhs (beta 〈B,ee〉 (S n)) x→veqb x d=false)
      (gamma_var (ν(S n+e_len ee)) (beta 〈B,ee〉 (S n)) P13))))
   〈aab,aae〉
  →(at (ssc a z (νn) P6)(Snoc Epsilon [νn←bb]))
   =plug_c
    (crc
     (pi1 Bite
      (λd:Bite
       .∀x:Variable
        .inb_b x (ssb Aab y (ν(n+S (e_len ee))) P7)=false
         →¬rhs (〈z,νn〉::beta_e ee (S n)) x→inb_b x d=false)
      (gamma_b (ssb Aab y (ν(n+S (e_len ee))) P7) (〈z,νn〉::beta_e ee (S n)) P8))
     (envc
      (pi1 Environment
       (λd:Environment
        .∀x:Variable
         .inb_e x (sse Aae y (ν(n+S (e_len ee))) P9)=false
          →¬rhs (〈z,νn〉::beta_e ee (S n)) x→inb_e x d=false)
       (gamma_e (sse Aae y (ν(n+S (e_len ee))) P9) (〈z,νn〉::beta_e ee (S n)) P14))
      (pi1 Variable
       (λd:Variable
        .∀x:Variable
         .veqb x (ν(n+S (e_len ee)))=false
          →¬rhs (〈z,νn〉::beta_e ee (S n)) x→veqb x d=false)
       (gamma_var (ν(n+S (e_len ee))) (〈z,νn〉::beta_e ee (S n)) P15))))
    (at (ssc 〈aab,aae〉 z (νn) P5)(Snoc Epsilon [νn←bb]))))
[ 2: #UU @UU ]
-P3 -P10 -P11 #P3 #P10 #P11 #P12

whd in match (gamma_b ? (?::?) ?);
whd in match (gamma_var ? (?::?) ?);
whd in match (gamma_e ? (?::?) ?);
(*
letin P13 ≝ (gamma_b_aux2 (ssb Aab y (ν(n+S (e_len ee))) P7) 〈z,νn〉 (beta_e ee (S n))
         P8)
letin P14 ≝ (gamma_b_aux3 (λl0:list (Variable×Variable).λb0:Bite.gamma_b b0 l0)
       (ssb Aab y (ν(n+S (e_len ee))) P7) (beta_e ee (S n)) z (νn) P8)
letin P15 ≝ (gamma_e_aux2 (sse Aae y (ν(n+S (e_len ee))) P9) 〈z,νn〉 (beta_e ee (S n))
          P11)
letin P16 ≝ (gamma_e_aux3
        (λl0:list (Variable×Variable).λe0:Environment.gamma_e e0 l0)
        (sse Aae y (ν(n+S (e_len ee))) P9) (beta_e ee (S n)) z (νn) P11)
letin P17 ≝ (gamma_var_aux2 (ν(n+S (e_len ee))) z (νn) (beta_e ee (S n)) P12)
*)
cut (∀P13, P14, P15, P16, P17.  
 (a
  =plug_c
   (crc
    (pi1 Bite ?
     (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta 〈B,ee〉 (S n)) P4))
    (envc
     (pi1 Environment ?
      (gamma_e (sse Aae y (ν(S n+e_len ee)) P2) (beta 〈B,ee〉 (S n)) P3))
     (pi1 Variable ?
      (gamma_var (ν(S n+e_len ee)) (beta 〈B,ee〉 (S n)) P10))))
   〈aab,aae〉
  →(at (ssc a z (νn) P6)(Snoc Epsilon [νn←bb]))
   =plug_c
    (crc
     (ssb
      (pi1 Bite ?
       (gamma_b (ssb Aab y (ν(n+S (e_len ee))) P7) (beta_e ee (S n)) P13)) z (νn) P14)
     (envc
      (sse
       (pi1 Environment ?
        (gamma_e (sse Aae y (ν(n+S (e_len ee))) P9) (beta_e ee (S n)) P15)) z (νn)
       P16)
      (if veqb
            (pi1 Variable ?
             (gamma_var (ν(n+S (e_len ee))) (beta_e ee (S n)) P17)) z 
       then (νn)
       else pi1 Variable ?
                (gamma_var (ν(n+S (e_len ee))) (beta_e ee (S n)) P17) )))
    (at (ssc 〈aab,aae〉 z (νn) P5) (Snoc Epsilon [νn←bb]))))
[ 2: #UU @UU ] 
-P8 -P11 -P12 #P8 #P11 #P12 #P13 #P14
whd in match (plug_c ? ?);
whd in match (plug_e ? ?);
whd in match (plug_c ? ?);
whd in match (plug_e ? ?);
>concat_e_epsilon -HI #HI destruct
whd in match (ssc ? ? ? ?);
whd in match (at ? ?);
whd in match (beta ? ?);
@eq_f2
[ letin TB ≝    (λd:Bite
    .∀x:Variable
     .inb_b x (ssb Aab y (ν(S n+e_len ee)) P1)=false
      →¬rhs (beta 〈B,ee〉 (S n)) x→inb_b x d=false)
  letin TE ≝ (λd:Environment
       .∀x:Variable
        .inb_e x (sse Aae y (ν(S n+e_len ee)) P2)=false
         →¬rhs (beta 〈B,ee〉 (S n)) x→inb_e x d=false)
  letin P15 ≝ (alpha_lemma2 (νn)
   (pi1 Bite TB (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta 〈B,ee〉 (S n)) P4))
   (concat
    (Snoc
     (pi1 Environment TE
      (gamma_e (sse Aae y (ν(S n+e_len ee)) P2) (beta 〈B,ee〉 (S n)) P3))
     [pi1 Variable
      (λd:Variable
       .∀x:Variable
        .veqb x (ν(S n+e_len ee))=false→¬rhs (beta 〈B,ee〉 (S n)) x→veqb x d=false)
      (gamma_var (ν(S n+e_len ee)) (beta 〈B,ee〉 (S n)) P10)←aab])
    aae)
   P6)
   letin TB' ≝ 
    (λd:Bite
     .∀x:Variable
      .inb_b x (ssb Aab y (ν(n+S (e_len ee))) P7)=false
       →¬rhs (beta_e ee (S n)) x→inb_b x d=false)
cut (n+S (e_len ee)= S n+ (e_len ee)) [ // ] #Heq
-P5 -P9 -P14
 cut (∀ P1, P4, P7, P8, P11, P15. (ssb
  (pi1 Bite ? (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta_e ee (S n)) P4)) z
  (νn) P15
  =ssb
   (pi1 Bite ? (gamma_b (ssb Aab y (ν(n+S (e_len ee))) P7) (beta_e ee (S n)) P8))
   z (νn) P11) )
  [ 2: #UU @UU ]
  >Heq #P1 #P4 #P7 #P8 #P11 #P15 //
|  whd in match (concat ? ?);
  >concat_e_epsilon @eq_f2 //
  letin TE ≝      (λd:Environment
      .∀x:Variable
       .inb_e x (sse Aae y (ν(S n+e_len ee)) P2)=false
        →¬rhs (beta_e ee (S n)) x→inb_e x d=false)
  letin TV ≝      (λd:Variable
      .∀x:Variable
       .veqb x (ν(S n+e_len ee))=false→¬rhs (beta_e ee (S n)) x→veqb x d=false)
  letin P15 ≝ (alpha_lemma1 (νn)
   (pi1 Bite
    (λd:Bite
     .∀x:Variable
      .inb_b x (ssb Aab y (ν(S n+e_len ee)) P1)=false
       →¬rhs (beta_e ee (S n)) x→inb_b x d=false)
    (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta_e ee (S n)) P4))
   (concat
    (Snoc
     (pi1 Environment TE
      (gamma_e (sse Aae y (ν(S n+e_len ee)) P2) (beta_e ee (S n)) P3))
     [pi1 Variable TV (gamma_var (ν(S n+e_len ee)) (beta_e ee (S n)) P10)←aab]) aae)
   P6)
  letin TE' ≝       (λd:Environment
       .∀x:Variable
        .inb_e x (sse Aae y (ν(n+S (e_len ee))) P9)=false
         →¬rhs (beta_e ee (S n)) x→inb_e x d=false)
  letin TV' ≝ (λd:Variable
            .∀x:Variable
             .veqb x (ν(n+S (e_len ee)))=false
              →¬rhs (beta_e ee (S n)) x→veqb x d=false)

(* letin P16 ≝ (alpha_lemma1 (νn)
    (gamma_b (ssb Aab y (ν(S n+e_len ee)) P1) (beta 〈B,ee〉 (S n)) P10)
    (concat
     (Snoc (gamma_e (sse Aae y (ν(S n+e_len ee)) P2) (beta 〈B,ee〉 (S n)) P4)
      [gamma_var (ν(S n+e_len ee)) (beta 〈B,ee〉 (S n)) P6←aab]) aae) P5)
 *)
  whd in match (beta ? ?);
  cut (∀P2, P3, P5, P9, P10, P12, P13, P14, P15. (sse
  (concat
   (Snoc
    (pi1 Environment ?
     (gamma_e (sse Aae y (ν(S n+e_len ee)) P2) (beta_e ee (S n)) P3))
    [pi1 Variable ? (gamma_var (ν(S n+e_len ee)) (beta_e ee (S n)) P10)←aab]) aae)
  z (νn) P15
  =concat
   (Snoc
    (sse
     (pi1 Environment ?
      (gamma_e (sse Aae y (ν(n+S (e_len ee))) P9) (beta_e ee (S n)) P12)) z (νn) P13)
    [if veqb
          (pi1 Variable ? (gamma_var (ν(n+S (e_len ee))) (beta_e ee (S n)) P14)) z 
     then (νn) 
     else pi1 Variable ? (gamma_var (ν(n+S (e_len ee))) (beta_e ee (S n)) P14) ←ssb aab z (νn) (alpha_lemma2 (νn) aab aae P5)])
   (sse aae z (νn) (alpha_lemma1 (νn) aab aae P5))))
   [ 2: #UUU @UUU ]
   cut (n+S (e_len ee)= S n+ (e_len ee)) [ // ] #Heq >Heq
   -P2 -P5 -P9 -P10 -P14
   #P2 #P3 #P5 #P9 #P10 #P12 #P13 #P14 #P15
  >sse_concat @eq_f2
    [ 2: //
    | whd in match (sse (Snoc ? ?) ? ? ?);
      >veqb_simm cases veqb 
      [ normalize //
      | normalize //
      ]
    ]
qed.

lemma alpha_c_to_alpha: ∀e, b, l, H. alpha_c 〈b, e〉 l H = alpha b e l H. // qed.

lemma gamma_v_aux1: ∀v.∀(H : ((∀x:Variable.rhs [] x→inb_v x v=false)∧distinct_rhs [])).
 (∀x:Variable.inb_v x v=false→¬rhs [] x→inb_v x v=false).
#c #H #k #HH #_ @HH qed.

lemma gamma_v_aux2: ∀v, hd, tl.∀(H : ((∀x:Variable.rhs (hd::tl) x→inb_v x v=false)∧distinct_rhs (hd::tl))).
((∀x:Variable.rhs tl x→inb_v x v=false)∧distinct_rhs tl).
#b #hd #t #H %
  [ #k #HH elim H #HHH #_ @HHH cases hd normalize #y #y' @or_intror @HH
  | elim H #_ cases hd normalize #y #y' * #_ //
  ]
qed.

lemma gamma_v_aux3:  
∀(gamma_v :
  (∀l:list (Variable×Variable)
   .∀v:Value
    .(∀x:Variable.rhs l x→inb_v x v=false)∧distinct_rhs l
     →Σd:Value.(∀x:Variable.inb_v x v=false→¬rhs l x→inb_v x d=false))).
 ∀(v : Value).
 ∀(t : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::t) x→inb_v x v=false)∧distinct_rhs (〈y,y'〉::t))).
 (inb_v y'
  (pi1 Value ?
   (gamma_v t v (gamma_v_aux2 v 〈y, y'〉 t H)))
  =false).
#gamma #c #t #y #y' #H cases (gamma ? ? ?) #gg #hh @hh
[ elim H #H' #_ @H' normalize >veqb_true @or_introl @refl
| elim H #_ normalize #H' elim H' //
] qed.

lemma gamma_v_aux4: ∀
 (gamma_v :
  (∀v:Value
   .∀l:list (Variable×Variable)
    .(∀x:Variable.rhs l x→inb_v x v=false)∧distinct_rhs l
     →Σd:Value.(∀x:Variable.inb_v x v=false→¬rhs l x→inb_v x d=false))).
 ∀(v : Value).
 ∀(tl : (list (Variable×Variable))).
 ∀(y : Variable).
 ∀(y' : Variable).
 ∀(H : ((∀x:Variable.rhs (〈y,y'〉::tl) x→inb_v x v=false)∧distinct_rhs (〈y,y'〉::tl))).
 (∀x:Variable
  .inb_v x v=false
   →¬rhs (〈y,y'〉::tl) x
    →inb_v x
     (ssv
      (pi1 Value
       (λd:Value.∀x0:Variable.inb_v x0 v=false→¬rhs tl x0→inb_v x0 d=false)
       (gamma_v v tl (gamma_v_aux2 v 〈y,y'〉 tl H))) y y'
      (gamma_v_aux3 (λl0:list (Variable×Variable).λv0:Value.gamma_v v0 l0) v tl
       y y' H))
     =false).

#gamma_b #b #tl #y #y' #H #x #Hinb #Hr
cut (∀J.   (inb_v x
  (ssv
   (pi1 Value ?
    (gamma_b b tl (gamma_v_aux2 b 〈y,y'〉 tl H))) y y' J)
  =false)) [ 2: #J @J ]
#J cases gamma_b in J ⊢%; #bb #h #J
lapply alpha_fin1 * * * * #_ #_ #_ #Hv #_ @Hv
[ @h [ @Hinb | % #abs elim Hr #Hr' @Hr' normalize @or_intror @abs ]
| elim Hr normalize >veqb_simm cases veqb // #abs @False_ind @abs @or_introl @refl ]
qed.

let rec gamma_v (v:Value) l on l : ((∀x. rhs l x → inb_v x v = false) ∧ distinct_rhs l) →
 (Σd. ∀x. inb_v x v = false → ¬rhs l x → inb_v x d = false) ≝ 
 match l return λl. ((∀x. rhs l x → inb_v x v = false) ∧ distinct_rhs l) →
 (Σd. ∀x. inb_v x v = false → ¬rhs l x → inb_v x d = false) with
 [ nil ⇒ λH. «v, gamma_v_aux1 … v H »
 | cons hd tl ⇒ match hd return λhd. (((∀x. rhs (hd::tl) x → inb_v x v = false) ∧ distinct_rhs (hd::tl)) →
  (Σd. ∀x. inb_v x v = false → ¬rhs (hd::tl) x → inb_v x d = false)) with 
  [ mk_Prod y y' ⇒ λH. «ssv (pi1 Value ? (gamma_v v tl (gamma_v_aux2 … H))) y y' (gamma_v_aux3 ? v tl y y' H), gamma_v_aux4 … H »  ]
 ] .

lemma gamma_vtovaraux: ∀l,x.∀(H : ((∀x0:Variable.rhs l x0→inb_v x0 (var x)=false)∧distinct_rhs l)).
 ((∀x0:Variable.rhs l x0→veqb x0 x=false)∧distinct_rhs l).
@list_ind // qed. 
 
lemma gamma_v_to_var: ∀l, x, H.
 pi1 … (gamma_v (var x) l H) = var (pi1 … (gamma_var x l (gamma_vtovaraux … H))).
@list_ind // * #y #y' #l #HI #x #H
whd in match (gamma_v ? ? ?);
whd in match (gamma_var ? ? ?);
generalize in match (gamma_v_aux2 ? ? ? ?);
generalize in match (gamma_v_aux2 ? ? ? ?);
generalize in match (gamma_v_aux3 ? ? ? ? ? ?); >HI
#P1
whd in match (ssv ? ? ? ?);
#P2 #P3 
cases (veqb ? y) // qed.

lemma gamma_e_step_aux1: ∀l,e,y,b. ∀(H : ((∀x:Variable.rhs l x→inb_e x (Snoc e [y←b])=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→veqb x y=false)∧distinct_rhs l).
 @list_ind [ #e #y #b #H % // #k normalize #abs @False_ind @abs ]
* #z #z' #tl #HI #e #y #b #H %
[ #k #Hk elim H #H' #_ lapply (H' … Hk) normalize cases veqb // normalize
  >if_monotone #H @H
| elim H #_ #HH @HH
] qed.

lemma gamma_e_step_aux2: ∀l,e,y,b. ∀(H : ((∀x:Variable.rhs l x→inb_e x (Snoc e [y←b])=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→inb_b x b=false)∧distinct_rhs l).
@list_ind [ #e #y #b #H % // #k normalize #abs @False_ind @abs ]
* #z #z' #tl #HI #e #y #b #H %
[ #k #Hk elim H #H' #_ lapply (H' … Hk) normalize cases inb_b //
  >if_monotone >if_monotone #H @H
| elim H #_ #HH @HH
] qed.

lemma gamma_e_step_aux3: ∀l,e,y,b. ∀(H : ((∀x:Variable.rhs l x→inb_e x (Snoc e [y←b])=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→inb_e x e=false)∧distinct_rhs l).
@list_ind [ #e #y #b #H % // #k normalize #abs @False_ind @abs ]
* #z #z' #tl #HI #e #y #b #H %
[ #k #Hk elim H #H' #_ lapply (H' … Hk) normalize cases inb_e // >if_t #H @H
| elim H #_ #HH @HH
] qed.

lemma gamma_e_step_aux4: ∀hd,tl,e,y,b. ∀(H :((∀x:Variable.rhs (hd::tl) x→inb_e x (Snoc e [y←b])=false))
   ∧distinct_rhs (hd::tl)).  
 ((∀x:Variable.rhs tl x→inb_e x (Snoc e [y←b])=false)∧distinct_rhs tl).
 #hd #tl #e #y #b #H %
[ #k #Hk elim H #H' #_ @H' cases hd #z #z' normalize @or_intror @Hk
| elim H #_ cases hd #z #z' normalize * #_ #H @H
] qed.

lemma gamma_e_step: ∀l, e, y, b, H.
 pi1 … (gamma_e (Snoc e [y←b]) l H) =
  Snoc (pi1 … (gamma_e e l (gamma_e_step_aux3 … H))) [(pi1 … (gamma_var y l (gamma_e_step_aux1 … H))) ← pi1 … (gamma_b b l (gamma_e_step_aux2 … H))]. 
@list_ind [ #e #y #b #H normalize @refl ]
* #z #z' #tl #HI #e #y #b #H
whd in match (gamma_e ? ? ?);
whd in match (gamma_e ? (?::?) ?);
whd in match (gamma_var ? ? ?);
whd in match (gamma_b ? ? ?);
generalize in match (gamma_e_aux3 ? ? ? ? ? ?);
generalize in match (gamma_e_aux2 ? ? ? ?);
>(HI … (gamma_e_step_aux4 … H)) #gea2 #gea3
whd in match (sse ? ? ? ?); >veqb_simm cases veqb //
qed.

lemma gamma_v_ns: ∀e,v,l,H. 
 (∀x. (domb_e x e=true) → inb_v x v = false) →
  pi1 … (gamma_v v (beta_e e l) H) = v.
@Environment_simple_ind2 // #e * * #y #b #HI #v #l #H #H1
whd in match (beta_e ? ?);
whd in match (gamma_v ? ? ?);
generalize in match (gamma_v_aux2 ? ? ? ?);
generalize in match (gamma_v_aux3 ? ? ? ? ? ?); >HI
[ lapply ssc_in * * * * #_ #_ #_ #Hv #_ #HH #HHH @Hv @(H1 (νy) ?)
  normalize >neqb_refl >if_t @refl
| #k #Hk @H1 normalize >Hk >if_monotone @refl
] qed.

lemma gamma_var_ns: ∀e,x,l,H. 
  (domb_e x e = false) → 
  pi1 … (gamma_var x (beta_e e l) H) = x.
@Environment_simple_ind2 // #e * * #y #b #HI #x #l #H #H1
whd in match (beta_e ? ?);
whd in match (gamma_var ? ? ?);
generalize in match (gamma_var_aux2 ? ? ? ? ?);
>HI
[ #H2 lapply H1 normalize cases veqb // normalize #abs destruct
| lapply H1 normalize cases domb_e // >if_monotone #H @H
| % // #k #Hk elim H #HH #_ @HH normalize @or_intror //
] qed.

lemma alpha_to_gamma_aux1: ∀b, e, n. ∀(H : (fresh_var 〈b,e〉≤n)).
 ((∀x:Variable.rhs (beta_e e n) x→inb_e x e=false)∧distinct_rhs (beta_e e n)).
#b #e #n #H % // #k #Hk lapply (beta_rhs_bound 〈b,e〉 n)
whd in match (beta ? ?); #Hbrb lapply Hk cases k #nk -Hk #Hk
lapply (Hbrb … Hk) * #Ha #Hb
change with (max ? ?≤n) in H;
lapply (transitive_le … (le_maxr … H) Ha)
lapply (fresh_var_to_in_crumble) * * * * #_ #_ #He #_ #_ @He
qed.

lemma alpha_to_gamma_aux2: ∀b, e, n. ∀(H : (fresh_var 〈b,e〉≤n)).
 ((∀x:Variable.rhs (beta_e e n) x→inb_b x b=false)∧distinct_rhs (beta_e e n)).
#b #e #n #H % // #k #Hk lapply (beta_rhs_bound 〈b,e〉 n)
whd in match (beta ? ?); #Hbrb lapply Hk cases k #nk -Hk #Hk
lapply (Hbrb … Hk) * #Ha #Hb
change with (max ? ?≤n) in H;
lapply (transitive_le … (le_maxl … H) Ha)
lapply (fresh_var_to_in_crumble) * * * * #_ #Hb #_ #_ #_ @Hb
qed.

lemma alpha_e_aux1:  ∀n.(∀m:ℕ.fresh_var_e Epsilon≤m∧m<n→inb_e (νm) Epsilon=false).
#n #m #_ // qed.

lemma alpha_e_aux2: ∀n, e', y, b', a.
 ∀(p : (fresh_var_e (Snoc e' [y←b'])≤n)).
 ∀(h : (∀m:ℕ.fresh_var_e e'≤m∧m<S n→inb_e (νm) a=false)).
 (inb_e (νn) a=false).
#n #e #y #b' #a #p #H @H % // change with (max ? ? ≤ n) in p; @(le_maxl … p) qed.

lemma alpha_e_aux3:  ∀n, e', y, b'. ∀(p : (fresh_var_e (Snoc e' [y←b'])≤n)).
 (fresh_var_e e'≤S n).
 #n #e' #y #b' #p change with (max ? ?≤n) in p; @(le_S … (le_maxl … p)) qed.
 
lemma alpha_e_aux4:
 ∀(alpha_e :
  (∀e:Environment
   .∀n:ℕ
    .fresh_var_e e≤n→Σd:Environment.(∀m:ℕ.fresh_var_e e≤m∧m<n→inb_e (νm) d=false))).
  ∀n, e', y, b', a.
 ∀(p : (fresh_var_e (Snoc e' [y←b'])≤n)).
 ∀(h : (∀m:ℕ.fresh_var_e e'≤m∧m<S n→inb_e (νm) a=false)).
  (∀m:ℕ
  .fresh_var_e (Snoc e' [y←b'])≤m∧m<n
   →inb_e (νm) (Snoc (sse a y (νn) (alpha_e_aux2 n e' y b' a p h)) [νn←b'])=false).
#alpha_e #n #e' #y #b' #a #p #h #m #H
lapply alpha_fin1 * * * * #_ #_ #He #_ #_ whd in match (inb_e ? ?);
cut (neqb m n = false)
[ cut (neqb m n = true ∨ neqb m n = false) // * #Hnm //
  elim (neqb_iff_eq m n) #Heq #_ lapply (Heq Hnm) -Heq #Heq destruct @False_ind
  elim H #_ @le_Sn_n ] #Hmn >He
[ normalize >Hmn normalize elim H cases y #ny
  #Ha #_ change with (max ? (max ? ?) ≤?) in Ha; lapply(le_maxr … (le_maxr … Ha))
  lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb
| normalize >neq_simm @Hmn 
| @h elim H #Ha #Hb % [ change with (max ? ? ≤?) in Ha; @(le_maxl … Ha) | @(le_S … Hb) ]
] qed.

let rec alpha_e  (e: Environment) (n: nat) on e:
 fresh_var_e e ≤ n → 
  Σd. ∀m. fresh_var_e e ≤ m ∧ m < n → inb_e (νm) d = false ≝ 
 match e return λe. fresh_var_e e ≤ n → Σd. ∀m. fresh_var_e e ≤ m ∧ m < n → inb_e (νm) d = false  with
 [ Epsilon ⇒ λp. mk_Sig … Epsilon ?
 | Snoc e' s ⇒ match s return λs. fresh_var_e (Snoc e' s) ≤ n → Σd. ∀m. fresh_var_e (Snoc e' s) ≤ m ∧ m < n → inb_e (νm) d = false with 
   [subst y b' ⇒ λp. match alpha_e e' (S n) (alpha_e_aux3 … p) with
     [ mk_Sig a h ⇒ mk_Sig … (Snoc (sse (a) y (νn) (alpha_e_aux2 … p h)) (subst (νn) b')) (alpha_e_aux4 alpha_e … p h) ]
   ]
 ].
 @(alpha_e_aux1 … n) qed.

lemma alpha_to_gamma_aux11: ∀b, e, n. ∀(H : (fresh_var 〈b,e〉≤n)). 
fresh_var_e e ≤n.
#b #e #n #H change with (max ? ?≤n) in H; @(le_maxr … H) qed.

lemma sse_proof_irrelevance: ∀e, z, z', H, H'. sse e z z' H = sse e z z' H'.
@Environment_simple_ind2 // #e * * #y #b #HI #z #z' #H #H' whd in match (sse ? ? ? ?);
cases veqb  qed.

lemma alpha_be_to_gamma_pre: ∀b, e, n, H, H1, H2. pi1 … (alpha b e n H) =
 〈pi1 … (gamma_b b (beta_e e n) H1), pi1 … (alpha_e e n H2)〉.
#b @Environment_simple_ind2 //
#e * * #y #b' #HI #n #H
whd in match (alpha b (Snoc ? ?) ? ?); #H1 #H2
lapply (HI (S n) ? ? ?)
[ @(le_S … (le_maxl … (le_maxr … H)))
| % // * #k #Hk lapply (betae_rhs_bound … Hk) * #Ha #_
  cut (fresh_var_b b ≤ k)
  [ @(transitive_le … (le_S … (le_maxl … H)) Ha)
  | lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb
  ] 
| 3: change with (max ? ? ≤ ?)
   change with (max ?  (max ? ?) ≤ n) in H; @to_max
  [ @(le_S … (le_maxl … H))
  |  @(le_S … (le_maxl … (le_maxr … H)))
  ]
|  cases alpha #C #E whd in match (match ? in Sig with [_⇒?]);  #HH destruct
  whd in match (ssc ? ? ? ?);
  whd in match (at ? ?); @eq_f2
  [ whd in match (gamma_b ? (cons ? ? ?) ?); //
  | whd in match (concat ? ?); >concat_e_epsilon whd in match (alpha_e ? ? ?);
    generalize in match (alpha_to_gamma_aux11 ? ? ? ?); #P1
        generalize in match (le_S ? ? ?); #P2
    
    whd in match (alpha_e (Snoc ? ?) ? ?);
        generalize in match (alpha_lemma1 ? ? ? ?);
        generalize in match (alpha_e_aux3 ? ? ? ? ?); #P3
 
    cut (alpha_e e (S n) P2 = alpha_e e (S n) P3) [ // ] #Heq >Heq
    cases (alpha_e ? ? ?) #AA #HH #P2
    whd in match (match  ? in Sig with [_⇒?]); @eq_f2 //
  ]
] qed.

lemma alpha_be_to_gamma: ∀b, e, n, H. pi1 … (alpha b e n H) =
 〈pi1 … (gamma_b b (beta_e e n) (alpha_to_gamma_aux2 b e n H)), pi1 … (alpha_e e n (alpha_to_gamma_aux11 b e n H))〉.
#b #e #n #H @alpha_be_to_gamma_pre qed.

lemma alphae_domain_bound: ∀ e, n, H, x.
 domb_e (νx) (pi1 … (alpha_e e n H)) = true →
  n ≤ x ∧ x ≤ n +e_len e.
@Environment_simple_ind2
[ #n normalize #_ #x #abs destruct
| #e * * #y #b' #HI #n #H #x
  whd in match (alpha_e ? ? ?);
  lapply (HI (S n) (alpha_e_aux3 … H))
  cases alpha_e #ae #h
  whd in match (match ? in Sig with [_⇒?]);
  -HI #HI
  whd in match (domb_e ? ?);
  whd in match (veqb ? ?);
  cut (neqb x n = true ∨ neqb x n = false) // * #Hxn >Hxn
  [ normalize elim (neqb_iff_eq x n) #Heq #_ lapply (Heq Hxn) -Heq #Heq
    destruct #_ % // ]
  >if_f #HH lapply (domb_sse … HH) *
  [ #Ha lapply (HI … Ha) * #Haa #Hb normalize % // @lt_to_le @Haa
  | * #Ha normalize #Hb elim (neqb_iff_eq x n) #Heq #_
    lapply (Heq Hb) * % //
  ]
] qed.

lemma alpha_domain_bound: ∀e, b, n, H, x.
 domb (νx) (pi1 … (alpha b e n H)) = true →
  n ≤ x ∧ x ≤ n +e_len e.
#e #b #n #H #x >alpha_be_to_gamma whd in match (domb ? ?);
@alphae_domain_bound qed. 

lemma dom_sse: ∀e, y, y', H. ∀x. domb_e x (sse e y y' H) = ((domb_e x e ∧ ¬veqb x y) ∨ (¬domb_e x e ∧ domb_e y e ∧ veqb x y')).
@Environment_simple_ind2 // #e * #z #b #HI #y #y' #H #x whd in match (sse ? ? ? ?);
whd in match (domb_e ? (Snoc ? ?)); whd in match (domb_e ? (Snoc ? ?));
cut (veqb y z = true ∨ veqb y z = false) // * #Hyz >Hyz 
[ >if_t whd in match (domb_e ? ?); >HI normalize >if_then_true_else_false
  elim (veqb_true_to_eq y z) #Heq #_ lapply (Heq Hyz) -Heq #Heq destruct
  cut (veqb x z = true ∨ veqb x z = false) // * #Hxz >Hxz
  [ >if_t >if_t >if_f >if_f elim (veqb_true_to_eq x z) #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct
    >if_monotone >if_f lapply H normalize >veqb_simm cases veqb // >if_t
    >if_monotone #abs destruct
  | >if_f >if_f >if_then_true_else_false cases veqb normalize cases domb_e //
  ]
| >if_f >if_f whd in ⊢ (? ? % ?); cut (veqb x z = true ∨ veqb x z = false) // * #Hxz
  [ elim (veqb_true_to_eq x z) #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct >Hxz
    >if_t >if_t >veqb_simm >Hyz normalize %
  | >Hxz >if_f >if_f >HI //
  ]
] qed.

lemma fvb_at: ∀e, b, e', x. fvb x (at 〈b, e'〉 e) = ((fvb x 〈b, e'〉 ∧ ¬ domb_e x e) ∨ fvb_e x e).
@Environment_simple_ind2
[ #b #e #x normalize cases fvb_b cases fvb_e // cases domb_e //
| #e * #y #b' #HI #b #e' #x
  lapply (HI b e' x) normalize >domb_concat_distr >fv_concat normalize
  cut (veqb x y = true ∨ veqb x y = false) // * #Hxy >Hxy normalize
  [ >if_monotone >if_monotone >if_monotone >if_f >if_f >if_f >if_monotone >if_f //
  | >if_then_true_else_false >if_then_true_else_false
    cases fvb_b normalize
    [ 2: #_ cases fvb_e // cases domb_e //
    | cases fvb_e cases domb_e // normalize
      [ #_ cases domb_e cases fvb_b //
      | cases domb_e //
      ]
    ]
  ]
] qed.

lemma fvb_ssc1:
 (∀c, y, y', x. ∀(H). veqb x y' = false → fvb x (ssc c y y' H) = (fvb x c ∧ (¬veqb x y))) ∧
  (∀b, y, y', x. ∀(H). veqb x y' = false → fvb_b x (ssb b y y' H) = (fvb_b x b ∧ (¬veqb x y))) ∧
   (∀e, y, y', x. ∀(H). veqb x y' = false → fvb_e x (sse e y y' H) = (fvb_e x e ∧ (¬veqb x y))) ∧
    (∀v, y, y', x. ∀(H). veqb x y' = false → fvb_v x (ssv v y y' H) = (fvb_v x v ∧ (¬veqb x y))) ∧
     (∀s, y, y', x. ∀(H). veqb x y' = false → fvb_s x (sss s y y' H) = (fvb_s x s ∧ (¬veqb x y))).
@Crumble_mutual_ind
[ #b #e #Hb #He #y #y' #x #H1 #H2 whd in match (ssc ? ? ? ?);
  whd in match (fvb ? ?); >Hb // >He //
  cut (veqb x y = true ∨ veqb x y = false) // * #Hxy >Hxy
  [ whd in match (andb ? false); >if_monotone
    whd in match (andb ? false); >if_monotone 
    whd in match (andb ? false); >if_monotone %
  | whd in match (andb ? true); >if_then_true_else_false
    whd in match (andb ? true); >if_then_true_else_false
    whd in match (andb ? true); >if_then_true_else_false >dom_sse >H2 >Hxy
    normalize cases fvb_b // cases domb_e // >if_monotone //
  ]
| #v #HI #y #y' #x #H #H1 @HI @H1
| #v #w #Hv #Hw #y #y' #x #H #H1 whd in match (ssb ? ? ? ?);
  whd in match (fvb_b ? ?); >Hv // >Hw // whd in match (fvb_b ? ?); cases fvb_v
  cases fvb_v // cases veqb //
| #z #y #y' #x #H #H1 normalize cut (veqb z y = true ∨ veqb z y = false) // * #Hyz >Hyz
  normalize
  [ >H1 elim (veqb_true_to_eq z y) #Heq #_ lapply (Heq Hyz) -Heq #Heq destruct
    cases veqb //
  | cut (veqb x z = true ∨ veqb x z = false) // * #Hxz >Hxz //
    elim (veqb_true_to_eq x z) #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct >Hyz
    //
  ]
| #z #c #HI #y #y' #x #H #H1 whd in match (ssv ? ? ? ?);
  cut (veqb z y = true ∨ veqb z y = false) // * #Hzy >Hzy
  [ >if_t normalize elim (veqb_true_to_eq z y) #Heq #_ lapply (Heq Hzy) -Heq #Heq
    destruct >veqb_simm cases veqb // cases fvb //
  | >if_f whd in match (((λp:inb_v y' (𝛌z.c)=false.𝛌z.ssc c y y' (alpha_lemma6 y' z c p)) H));
    whd in match (fvb_v ? ?); whd in match (fvb_v ? ?);
    cut (veqb z x = true ∨ veqb z x = false) // * #Hzx >Hzx // >if_t >if_t
    >HI //
  ]
| //
| #e * #z #b' #He #Hs #y #y' #x #H #H1 whd in match (sse ? ? ? ?);
  cut (veqb y z = true ∨ veqb y z = false) // * #Hyz >Hyz
  [ >if_t whd in match (((λp:inb_e y' (Snoc e [z←b'])=false
    .Snoc (sse e y y' (alpha_lemma8 y' e z b' p))
     [y'←ssb b' y y' (alpha_lemma7 y' e z b' p)]) H));
  whd in match (fvb_e ? ?); >He //
  lapply (Hs y y' x ? H1)
  [ lapply H change with (orb ? ?) in match (inb_e ? ?);
    cases inb_s // whd in match (orb ? true); >if_monotone //
  | whd in match (sss ? ? ? ?);
    whd in match (fvb_s ? ?);
    cut (∀Z, Z'. fvb_b x (ssb b' y y' Z) = fvb_b x (ssb b' y y' Z')) [ // ]
    #Htmp >(Htmp ? (alpha_lemma7 … H)) #HH >HH normalize -Htmp -HH
    elim (veqb_true_to_eq … y z) #Heq #_ lapply (Heq Hyz) -Heq #Heq destruct
    cut (veqb x z = true ∨ veqb x z = false) // * #Hxz >Hxz normalize
    [ >if_monotone >if_monotone >if_f //
    | >if_then_true_else_false >if_then_true_else_false >if_then_true_else_false
      >H1 >if_f cases fvb_e //
    ]
  ]
  | >if_f whd in match 
  ((λp:inb_e y' (Snoc e [z←b'])=false
    .Snoc (sse e y y' (alpha_lemma8 y' e z b' p))
     [z←ssb b' y y' (alpha_lemma7 y' e z b' p)]) H);
    whd in match (fvb_e ? ?); whd in match (fvb_e ? (Snoc ? ?)); >He //
    lapply (Hs y y' x ? H1)
  [ lapply H change with (orb ? ?) in match (inb_e ? ?);
    cases inb_s // whd in match (orb ? true); >if_monotone //
  | whd in match (sss ? ? ? ?);
    whd in match (fvb_s ? ?);
    cut (∀Z, Z'. fvb_b x (ssb b' y y' Z) = fvb_b x (ssb b' y y' Z')) [ // ]
    #Htmp >(Htmp ? (alpha_lemma7 … H)) #HH >HH -Htmp -HH
    whd in match (fvb_s ? ?);
    cases veqb
    [ whd in match (andb ? false); >if_monotone
      whd in match (andb ? false); >if_monotone
      whd in match (andb ? false); >if_monotone //
    | cases veqb
      [ whd in match (andb ? false); >if_monotone
        whd in match (andb ? false); >if_monotone //
      | whd in match (andb ? true); >if_then_true_else_false
        whd in match (andb ? true); >if_then_true_else_false
        whd in match (andb ? true); >if_then_true_else_false
        whd in match (andb ? true); >if_then_true_else_false //
      ]
    ]
  ]
  ]
| #z #b #HI #y #y' #x #H #H1 normalize >HI //
] qed. 
  
lemma alpha_fv_cons: ∀e, b, n, H. ∀x. fvb x (pi1 … (alpha b e n H)) = fvb x 〈b, e〉.
@Environment_simple_ind2
[ #b #n change with (max ? ?) in match (fresh_var ?); #H #x whd in match (alpha ? ? ? ?); //
| #e * * #y #b' #HI #b #n change with (max ? (max ? (max ? ?))) in match (fresh_var ?);
  #H #x whd in match (alpha ? ? ? ?); lapply (HI b (S n) (alpha_aux1 b e [νy←b'] n H) x)
  cases alpha * #ab #ae #hh whd in match (match ? in Sig with [_⇒?]);
  change with (at (CCrumble b e) (Snoc Epsilon [νy←b'])) in match (CCrumble b (Snoc e [νy←b']));
  #HH <HH >fvb_at >fvb_at whd in match (fvb_e ? ?); whd in match (domb_e ? ?);
  whd in match (domb_e ? ?); >if_then_true_else_false
  whd in match (domb_e ? ?); whd in match (domb_e ? ?); >if_then_true_else_false
  cases fvb_b
  [ whd in match (orb ? true); >if_monotone
    whd in match (orb ? true); >if_monotone % ]
  whd in match (orb ? false); >if_then_true_else_false
  whd in match (orb ? false); >if_then_true_else_false <HH
  cut (veqb x (νn) = true ∨ veqb x (νn) = false) // * #Hxn
  [ elim (veqb_true_to_eq … x νn) #Heq lapply (Heq Hxn) -Heq #Heq destruct #_
    >Hxn whd in match (notb true); whd in match (andb ? false); >if_monotone
    >HH
    cut (inb (νn)  〈b,e〉 = false)
    [ lapply fresh_var_to_in_crumble * * * * #Hc #_ #_ #_ #_ @Hc 
      @to_max [ @(le_maxl … H) | @(le_maxl … (le_maxr … H)) ] ] #Hin
    cut (fvb (νn)  〈b,e〉 = false)
    [ lapply Hin @bool_impl_inv2 lapply fv_to_in_crumble * * * * #Hc #_ #_ #_ #_
      @Hc ] -Hin #Hfv >Hfv whd in match (andb false ?); % ]
  lapply fvb_ssc1 * * * * #_ #Hb #He #_ #_
  whd in match (fvb ? ?); >Hb // >He //  >dom_sse cases veqb
  [ whd in match (andb ? false); >if_monotone
    whd in match (andb ? false); >if_monotone
    whd in match (andb ? false); >if_monotone
    whd in match (andb false ?); //
  | whd in match (andb ? true); >if_then_true_else_false
    whd in match (andb ? true); >if_then_true_else_false
    whd in match (andb ? true); >if_then_true_else_false
    whd in match (andb ? true); >if_then_true_else_false >Hxn
    whd in match (andb ? false); >if_monotone
    whd in match (andb ? true); >if_then_true_else_false
    whd in match (orb ? false); >if_then_true_else_false //
  ]
] qed.

lemma ss_fresh_var:
(∀c, n, x, H. fresh_var (ssc c x (νn) H) ≤ max (fresh_var c) (S n)) ∧
(∀c, n, x, H. fresh_var_b (ssb c x (νn) H) ≤ max (fresh_var_b c) (S n)) ∧
(∀c, n, x, H. fresh_var_e (sse c x (νn) H) ≤ max (fresh_var_e c) (S n)) ∧
(∀c, n, x, H. fresh_var_v (ssv c x (νn) H) ≤ max (fresh_var_v c) (S n)) ∧
(∀c, n, x, H. fresh_var_s (sss c x (νn) H) ≤ max (fresh_var_s c) (S n)).
@Crumble_mutual_ind
[ #b #e #Hb #He #n #x #H whd in match (ssc ? ? ? ?);
  change with (max ? ?) in match (fresh_var ?);
  @to_max
  [ change with (max ? ?) in match (fresh_var ?); >max_swap2 @max_add @Hb
  | change with (max ? ?) in match (fresh_var ?); 
     >max_comm in match (max (fresh_var_b ?) ?); >max_swap2 @max_add @He
  ]
| #v #HI #n #x #H whd in match (ssb ? ? ? ?);
  whd in match (fresh_var_b ?);
  @HI
| #v #w #Hv #Hw #n #x #H whd in match (ssb ? ? ? ?); 
  change with (max ? ?) in match (fresh_var_b ?);
  change with (max ? ?) in match (fresh_var_b ?); @to_max
  [ change with (max ? ?) in match (fresh_var ?); >max_swap2 @max_add @Hv
  | change with (max ? ?) in match (fresh_var ?); 
     >max_comm in match (max (fresh_var_v ?) ?); >max_swap2 @max_add @Hw
  ]
| * #z #n * #x #H whd in match (ssv ? ? ? ?);
  whd in match (fresh_var_v (var ?));
  whd in match (veqb ? ?);
  cut (neqb z x = true ∨ neqb z x = false) // * #Htf >Htf
  [ elim (neqb_iff_eq z x) #Heq #_ lapply (Heq Htf) -Heq #Heq destruct
    >if_t whd in match (fresh_var_v ?); //
  | >if_f whd in match (fresh_var_v ?); //
  ]
| * #z #c #HI #n * #x #H whd in match (ssv ? ? ? ?);
  whd in match (veqb ? ?);
  cut (neqb z x = true ∨ neqb z x = false) // * #Htf >Htf
  [ >if_t //
  | >if_f
    change with (fresh_var_v (𝛌νz.ssc c (νx) (νn) (alpha_lemma6 (νn) (νz) c H)))
     in match (fresh_var_v ?);
    change with (max ? ?) in match (fresh_var_v ?);
    change with (max ? ?) in match (fresh_var_v ?); @to_max // >max_comm in match (max (S z) ?);
    <max_swap2 @max_add @HI
  ]
| //
| #e * * #y #b #He #Hs #n #x #H whd in match (sse ? ? ? ?); cases veqb
  [ >if_t change with (max ? ?) in match (fresh_var_e ?);
    change with (max ? ?) in match (fresh_var_e (Snoc e [νy←b])); @to_max
    [ >max_swap2 @max_add @He
    | >max_comm in match (max (fresh_var_e ?) ?); >max_swap2 @max_add @to_max
      [ //
      | lapply ((Hs n x ?)) [ @(And_ind … (orb_false … H)) #_ #h @h]
        whd in match (sss ? ? ? ?);
        change with (max ? ?) in match (fresh_var_s ?);  #HH
        lapply (le_maxr … HH) 
        cut (∀b, x, n, H, K. ssb b x n H =ssb b x n K) // #HH
        >(HH ? ? ? ? (alpha_lemma7 (νn) e (νy) b H)) //
      ]
    ]
  | >if_f change with (max ? ?) in match (fresh_var_e ?);
    change with (max ? ?) in match (fresh_var_e (Snoc e [νy←b])); @to_max
    [ >max_swap2 @max_add @He
    | >max_comm in match (max (fresh_var_e ?) ?); >max_swap2 @max_add @Hs
      elim (orb_false … H) //
    ]
  ]
| * #x #b #HI #n #y #H whd in match (sss ? ? ? ?);
  change with (max ? ?) in match (fresh_var_s ?);
  change with (max ? ?) in match (fresh_var_s ?); @to_max //
  >max_comm in match (max (S x) ?); >max_swap2 @max_add @HI
] qed.

lemma alpha_fresh_var: ∀e, b, n, H. fresh_var (pi1 … (alpha b e n H)) ≤ n+e_len e.
@Environment_simple_ind2
[ #b #n #H normalize cases leb // normalize @(le_plus_a_r O … (le_maxl … H))
| #e * * #y #b' #HI #b #n #H
  whd in match (alpha ? ? ? ?);
  lapply (HI b (S n) (alpha_aux1 b e [νy←b'] n H))
  generalize in match (alpha b e (S n) (alpha_aux1 b e [νy←b'] n H)); *
  #a #h whd in match (match ? in Sig with [_⇒?]);
  whd in match (at ? ?);
  lapply h cases a #ab #ae -h #h #H2
  whd in match (ssc ? ? ? ?);
  whd in match (match ? in Crumble with [_⇒?]);
  whd in match (concat ? ?); >concat_e_epsilon
  whd in match (e_len ?);
  lapply ss_fresh_var * * * * #_ #Hb #He #_ #_
  change with (max ? ?) in match (fresh_var ?); @to_max
  [ lapply (Hb ab n (νy) (alpha_lemma2 (νn) ab ae (alpha_aux3 b e (CCrumble ab ae) n (νy) b' h H)))
   #Hb' <plus_n_Sm change with (S n + e_len e) in match (S ?);
   cut (max (fresh_var_b ab) (S n) ≤ S n+e_len e)
   [ @to_max // @(le_maxl … H2)] #Hb'' @(transitive_le … Hb' Hb'')
  | @to_max
    [ lapply (He ae n (νy) (alpha_lemma1 (νn) ab ae (alpha_aux3 b e 〈ab,ae〉 n (νy) b' h H)))
      #He' <plus_n_Sm change with (S n + e_len e) in match (S ?);
      cut (max (fresh_var_e ae) (S n) ≤ S n+e_len e)
   [ @to_max // @(le_maxr … H2)] #He'' @(transitive_le … He' He'') ]
   <plus_n_Sm change with (S n + e_len e) in match (S ?); @to_max
   // @le_plus_a_r @le_S @(le_maxr …(le_maxr … (le_maxr … H)))
  ]
] qed.

lemma alphae_fresh_var: ∀e, n, H. fresh_var_e (pi1 … (alpha_e e n H)) ≤ n+e_len e.
@Environment_simple_ind2
[ #n #H normalize cases leb // normalize @(le_plus_a_r O … (le_maxl … H))
| #e * * #y #b' #HI #n #H
  whd in match (alpha_e ? ? ?);
  lapply (HI (S n) (alpha_e_aux3 n e (νy) b' H))
  generalize in match (alpha_e e (S n) (alpha_e_aux3 n e (νy) b' H)); *
  #a #h whd in match (match ? in Sig with [_⇒?]);
  whd in match (at ? ?); #H2
  whd in match (e_len ?);
  lapply ss_fresh_var * * * * #_ #_ #He #_ #Hs
  change with (max ? ?) in match (fresh_var ?); @to_max
  [ lapply (He a n (νy) (alpha_e_aux2 n e (νy) b' a H h))
   #Hb' <plus_n_Sm change with (S n + e_len e) in match (S ?);
   cut (max (fresh_var_e a) (S n) ≤ S n+e_len e)
   [ @to_max // @(le_maxl … H2)] #Hb'' @(transitive_le … Hb' Hb'')
  | @to_max
    [ <plus_n_Sm @le_S_S @le_plus_a_r @le_n
    | <plus_n_Sm change with (S n + e_len e) in match (S ?); @le_S
      @le_plus_a_r @(le_maxr … (le_maxr … H))
  ]
] qed.


lemma lt_to_le1:  ∀n:ℕ.∀m:ℕ.n<m→n≤m.
@lt_to_le qed.

lemma ssss_aux1: ∀z, e, w, b. (inb_e z (Snoc e [w←b])=false) → (inb_s z [w←b]=false).
#z #e #w #b change with (orb ? ?) in match (inb_e ? ?); cases inb_s //
normalize >if_monotone // qed.

lemma ss_over_ss:
(∀c, x, y, z, H1, H2, H3. ssc (ssc c x y H1) y z H2 = ssc c x z H3) ∧
(∀b, x, y, z, H1, H2, H3. ssb (ssb b x y H1) y z H2 = ssb b x z H3) ∧
(∀e, x, y, z, H1, H2, H3. sse (sse e x y H1) y z H2 = sse e x z H3) ∧
(∀v, x, y, z, H1, H2, H3. ssv (ssv v x y H1) y z H2 = ssv v x z H3) ∧
(∀s, x, y, z, H1, H2, H3. sss (sss s x y H1) y z H2 = sss s x z H3).
@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #z #H1 #H2 #H3 
  whd in match (ssc ? ? ? ?);
  whd in match (ssc ? ? ? ?); //
| #v #HI #x #y #z #H1 #H2 #H3 
  whd in match (ssb ? ? ? ?);
  whd in match (ssb ? ? ? ?); @eq_f >HI //
| #v #w #Hv #Hw #x #y #z #H1 #H2 #H3
  whd in match (ssb ? ? ? ?);
  whd in match (ssb ? ? ? ?); //
| #w #x #y #z  normalize cases (veqb w x) #H1 #H2 #H3
  normalize [>veqb_true >if_t // 
  | >veqb_simm >H1 //
  ]
| #w #c #HI #x #y #z #H1
  whd in match (ssv (lambda ? ?) ? ? ?);
  cut (veqb w x = true ∨ veqb w x = false) // * #Htf 
  [ >Htf >if_t elim (veqb_true_to_eq w x) #Heq lapply (Heq Htf) -Heq #Heq
    destruct #_ #H2 #H3  normalize >veqb_true normalize
    cut (veqb x y = false) [ lapply H1 normalize cases inb
      [ >if_monotone #abs destruct
      | >if_then_true_else_false // ]
      | #Htt >Htt >if_f normalize @eq_f2 //
        lapply ssc_in * * * * #Hc #_ #_ #_ #_ @Hc lapply H1 
        normalize cases inb // >if_monotone //
      ]
  | >Htf >if_f #H2 #H3 whd in match (ssv ? ? ? ?);
    whd in match (ssv ? ? ? ?); >Htf >if_f
    cut (veqb w y = false) [ lapply H1 normalize >veqb_comm cases veqb // >if_t //
    | #HH >HH >if_f normalize >HI //
    ]
  ]
| //
| #e * #w #b #He #Hs #x #y #z #H1
  whd in match (sse (Snoc ? ?) ? ? ?); #H2 #H3
    whd in match (sse (Snoc ? ?) ? ? ?);

  cut (veqb x w = true ∨ veqb x w = false) // * #Htf 
  [ >Htf in H2 ⊢ %;  >if_t elim (veqb_true_to_eq x w) #Heq lapply (Heq Htf) -Heq #Heq
    destruct #_ #H2 >if_t
    whd in match (sse ? ? ? ?); >veqb_true >if_t
    change with (Snoc ? ? = Snoc ? ?) @eq_f2 //
    @eq_f2 // lapply (Hs w y z ? ? ?)
    [@(ssss_aux1 … H3)
    | whd in match (sss ? ? ? ?);
      change with (orb ? ?) in match (inb_s ? ?);
      cut (veqb z w = false)
      [ lapply H3 normalize cases veqb normalize // >if_monotone //
      | #Hf >Hf normalize 
        cut (∀K. (inb_b z (ssb b w y K)) = false) [2: #uu @uu]
        #K lapply H2
        change with (orb ? ?) in match (inb_e ? ?);
        change with (orb ? ?) in match (inb_s ? ?);
        cut (∀J, K. inb_b z (ssb b w y K) = inb_b z (ssb b w y J)) //
        #HH <(HH K) [ cases inb_b [ normalize >if_monotone >if_monotone // | // ]
        | @K ]
      ]
    | @(ssss_aux1 … H1) ]
    whd in match (sss ? ? ? ?); whd in match (sss ? ? ? ?); #HH destruct -HH
    cut (∀P. ssb b w z P = ssb b w z (alpha_lemma7 z e w b H3)) // #HH
    <HH <e0 //
  | >Htf in H2 ⊢%; >if_f >if_f #H2
    whd in match (sse ? ? ? ?);
    cut (veqb y w = false)
    [ lapply H1 normalize cases veqb // >if_t >if_monotone //
    | #Htf >Htf >if_f change with (Snoc ? ? = Snoc ? ?) @eq_f2 //
      @eq_f2 // lapply (Hs x y z ? ? ?)
    [@(ssss_aux1 … H3)
    | whd in match (sss ? ? ? ?);
      change with (orb ? ?) in match (inb_s ? ?);
      cut (veqb z w = false)
      [ lapply H3 normalize cases veqb normalize // >if_monotone //
      | #Hf >Hf normalize 
        cut (∀K. (inb_b z (ssb b x y K)) = false) [2: #uu @uu]
        #K lapply H2
        change with (orb ? ?) in match (inb_e ? ?);
        change with (orb ? ?) in match (inb_s ? ?);
        cut (∀J, K. inb_b z (ssb b w y K) = inb_b z (ssb b w y J)) //
        #HH <(HH K) [ cases inb_b [ normalize >if_monotone >if_monotone // | // ]
        | @K ]
      ]
    | @(ssss_aux1 … H1) ]
    whd in match (sss ? ? ? ?); whd in match (sss ? ? ? ?); #HH destruct -HH
    cut (∀P. ssb b w z P = ssb b w z (alpha_lemma7 z e w b H3)) // #HH
    <HH <e0 // -e0 lapply H3 normalize cases inb_b // >if_monotone >if_monotone //
    ]
  ]
| #w #b #Hb #x #y #z #H1 #H2 #H3 normalize @eq_f2 // @Hb
] qed.

lemma aetg_aux1: ∀e, y, b, n. (fresh_var_e (Snoc e [y←b])≤n)→ ((∀x:Variable.rhs (beta_e (Snoc e [y←b]) n) x→inb_e x (Snoc e [y←b])=false)
   ∧distinct_rhs (beta_e (Snoc e [y←b]) n)) →
 ((∀x:Variable.rhs (beta_e e (S n)) x→inb_e x e=false)
  ∧distinct_rhs (beta_e e (S n))).
#e * #y #b #n #J #H % // * #x whd in match (beta_e ? ?); #Hk lapply (betae_rhs_bound e (S n) x)
#KK lapply (KK Hk) * #HJ #_
cut (fresh_var_e e ≤x)
[@(transitive_le … (le_S …(le_maxl … J)) HJ)
| lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_ @He
]qed.
  
(*
lemma aa_aux1: ∀e, b, x, y, m.∀ (D :inb x 〈b,e〉=false). ∀A. ∀ AL2, GBA2, GBA3, AL22.
 (ssb
  (pi1 Bite ?
   (gamma_b (ssb b y x AL2)
    (beta_e
     (sse e y x (alpha_lemma1 x b e ?))
     (S m))
    GBA2))
  x (νm) GBA3
  =ssb
   (pi1 Bite
    (λd:Bite
     .∀x:Variable.inb_b x b=false→¬rhs (beta_e e (S m)) x→inb_b x d=false)
    (gamma_b b (beta_e e (S m)) A)) y
   (νm) AL22). [2:@D]
@Environment_simple_ind2
[ #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #H9 #H10
  whd in match (sse Epsilon ? ? ?);
  whd in match (beta_e Epsilon ?);
  whd in match (gamma_b ? ? ?);
  whd in match (gamma_b ? ? ?);
  lapply ss_over_ss * * * * #_ #Hb #_ #_ #_ @Hb
| #e * * #z #bb #HI #b #x #y #m #H
  whd in match (sse ? ? ? ?);
  whd in match (beta_e (Snoc ? ?) ?);  #A
  whd in match (gamma_b ? ? ?);
  whd in match (gamma_b ? (?::?) ?);
  cut (veqb y (νz) =true ∨ veqb y (νz) =false) // * #Htf
  >Htf
  [ >if_t whd in match (beta_e ? ?); #AL2 #GBA2
  whd in match (gamma_b ? (?::?) ?);
  whd in match (gamma_b ? (?::?) ?); >HI
  

lemma alphae_absorbance: ∀e, n, m, H, H'.∀ K: n + (e_len e) ≤ m.
 pi1 … (alpha_e … (pi1 … (alpha_e e n H)) m H') = pi1 … (alpha_e e m ?).
[ 2: @(transitive_le … (le_plus_a_r (e_len e) … H) K)]
@Environment_simple_ind2
[//
| #e * #y #b #HI #n #m #H #H' #K
  whd in match (alpha_e ? n H);
  whd in match (alpha_e (Snoc ? ?) m ?);
  lapply (HI (S n) (S m) ? ? ?)
  [ 3: @(alpha_e_aux3 n e y b H)
  | @le_S lapply K <plus_n_Sm //
  | lapply (alphae_fresh_var e (S n) (le_S … (le_maxl … H))) #HH
    lapply K whd in match (e_len ?); <plus_n_Sm
    #KK @(le_S … (transitive_le … HH KK ))]
  #HII
  cut (∀a, c, J, K. alpha_e a c K = alpha_e a c J) // #alpha_pi
  lapply HII 
  <(alpha_pi e (S m)) [2: @(alpha_e_aux3 m e y b
     (transitive_le (fresh_var_e (Snoc e [y←b])) (n+e_len (Snoc e [y←b])) m
      (le_plus_a_r (e_len (Snoc e [y←b])) (fresh_var_e (Snoc e [y←b])) n H) K))]
  cases (alpha_e e (S m) ?) #ee #hh
  whd  in match (match «ee,hh»
     in Sig
     with 
    [mk_Sig
     (a:Environment)
      
     (h:?)⇒
     «Snoc
      (sse a y (νm)
       (alpha_e_aux2 m e y b a
        (transitive_le (fresh_var_e (Snoc e [y←b])) (n+e_len (Snoc e [y←b])) m
         (le_plus_a_r (e_len (Snoc e [y←b])) (fresh_var_e (Snoc e [y←b])) n H) K)
        h))
      [νm←b],
     alpha_e_aux4 alpha_e m e y b a
     (transitive_le (fresh_var_e (Snoc e [y←b])) (n+e_len (Snoc e [y←b])) m
      (le_plus_a_r (e_len (Snoc e [y←b])) (fresh_var_e (Snoc e [y←b])) n H) K) h»]);
  whd in match (alpha_e ? ? ?) in H';
  generalize in match (?:(fresh_var_e
  (pi1 Environment
   (λd:Environment.∀m0:ℕ.fresh_var_e e≤m0∧m0<S n→inb_e (νm0) d=false)
   (alpha_e e (S n) (alpha_e_aux3 n e y b H)))
  ≤S m)); #LL
  cases (alpha_e e (S n) (alpha_e_aux3 n e y b H)) in H' LL ⊢%; #ff #jj
  whd in match ( match «ff,jj»
          in Sig
          with 
         [mk_Sig
          (a:Environment)
           
          (h:(∀m0:ℕ.fresh_var_e e≤m0∧m0<S n→inb_e (νm0) a=false))⇒
          «Snoc (sse a y (νn) (alpha_e_aux2 n e y b a H h)) [νn←b],
          alpha_e_aux4 alpha_e n e y b a H h»]); #H' #LL
  whd in match (alpha_e (Snoc ? ?) ? ?);*)
  

definition alpha2_c ≝ λc, n. match c with [CCrumble b e ⇒ λH. alpha2 b e n H].

lemma aca2c: ∀c, n, H. alpha2_c c n H = alpha_c c n H. * #b #e #n #H
change with (alpha ? ? ? ?) in match (alpha_c ? ? ?);
change with (alpha2 ? ? ? ?) in match (alpha2_c ? ? ?); /2/ qed.
(*
lemma alpha_absorbance: ∀e, b, n, m, d. ∀H1, H2, H3. ∀ K: n + (e_len_c 〈b, e〉) ≤ m.
∀(R: d = pi1 … (alpha2_c 〈b, e〉 n H1)). 
pi1 … (alpha2_c 〈b, e〉 m H2) = pi1 … (alpha2_c d m H3).
@Environment_simple_ind2
[ #b #n #m #d #H1 #H2 #H3 #K whd in match (alpha2_c ? ? ?); #Heq  <Heq in H2 ⊢%; #l //
| #e * #y #b' #HI #b #n #m * #db #de #H #H' #K
  whd in match (alpha2_c ? ? ?);
  whd in match (at ? ?);             
  whd in match (alpha2_c 〈db, de〉 ? ?); 
  whd in match (alpha2_c 〈b, Snoc e ?〉 ? ?);
  whd in match (at ? (Snoc Epsilon [?←b'] )); 
  *)

(*
lemma alpha_e_concat_aux1: ∀f, e, n.
 fresh_var_e (concat e f) ≤ n → fresh_var_e e ≤ (n+e_len f).
#f #e #n >fresh_var_concat #H lapply (le_maxl … H)
cut (n ≤ n + e_len f) [// ] #H2 #H1 @(transitive_le … H1 H2) qed.

lemma alpha_e_concat_aux2: ∀f, e, n.
 fresh_var_e (concat e f) ≤ n → fresh_var_e f ≤ (n).
#f #e #n >fresh_var_concat #H @(le_maxr … H) qed.

lemma alpha_e_step: ∀e, y, b, n, H.
 pi1 … (alpha_e (Snoc e [y←b]) n H) = Snoc (pi1 … (alpha_e e (S n) (alpha_e_aux3 … H))) [νn←b].
@Environment_simple_ind2
[ #y #b #n #H whd in match (alpha_e ? ? ?); whd in match (sse ? ? ? ?); //
| #e #s #HI #y #b #n whd in match (alpha_e ? ? ?);


lemma alpha_e_concat: ∀f, e, n, H. 
 pi1 … (alpha_e (concat e f) n H) = concat (pi1 … (gamma_e e (beta concat e f ))) (pi1 … (alpha_e f n (alpha_e_concat_aux2 … H))).

@Environment_simple_ind2
[ #e #n whd in match (concat ? ?); #H
  whd in match (alpha_e Epsilon … n (alpha_e_concat_aux2 …)); >concat_e_epsilon
  whd in match (e_len Epsilon);
  generalize in match (alpha_e_concat_aux1 ? ? ? ?);
  generalize in match (H);
  cut (n+0=n) [//] #HH >HH //
| #f * #y #b #HI #e #n whd in match (concat ? ?); #H
  whd in match (alpha_e ? ? ?);
  lapply (HI e (S n) (alpha_e_aux3 n (concat e f) y b H))
  cases alpha_e #a #h
  whd in match (match ?  in Sig with [_⇒?]); #Heq
  generalize in match (alpha_e_aux2 ? ? ? ? ? ? ?); >Heq #aea2
  >sse_concat
  whd in match (alpha_e (Snoc ? ?) ? ?);
  [ change with (max ? ?≤n) in H; @
  


lemma alpha_crumble_aux1: ∀b,e,n. fresh_var (at 〈b,e〉 Epsilon)≤n → (fresh_var 〈b,e〉≤n).
#b #e #n normalize #H @H qed.

lemma alpha_crumble_aux2: ∀a,b,c,e1,n,y.
 (∀m:ℕ.fresh_var (at c e1)≤m∧m<S n→inb (νm) a=false) → 
 (fresh_var (at c (Snoc e1 [y←b]))≤n) →  (inb (νn) a=false).
#a #b #c #e1 #n #y #h #H @h normalize % // lapply H cases c #b #ee
whd in match (at ? ?);
lapply fresh_var_distr_crumble * * * * #Hdc #_ #_ #_ #_
#HH lapply (Hdc … HH) * #Hb #He lapply He >fresh_var_concat -Hdc -He #He
change with (max ? ?≤n) @to_max // >fresh_var_concat 
@to_max [@(le_maxl … He) ]
change with (max ? ?) in match (fresh_var_e (Snoc ? ?)) in He; @(le_maxl … (le_maxr … He)) qed.

lemma alpha_crumble_aux4: ∀b,c,e1,n,y. fresh_var (at c (Snoc e1 [y←b]))≤n →
 (fresh_var (at c e1)≤S n).
#b * #bb #ee #e1 #n #y
whd in match (at ? ?); whd in match (at ? ?); 
lapply fresh_var_distr_crumble * * * * #Hdc #_ #_ #_ #_ #H
lapply (Hdc … H) * #Hbb >fresh_var_concat #Hee change with (max ? ? ≤S n)
@to_max
[ @(le_S … Hbb)
| >fresh_var_concat @to_max
  [ @(le_S … (le_maxl … Hee)) 
  | change with (max ? ?) in match (fresh_var_e (Snoc ? ?)) in Hee;
    @(le_S … (le_maxl … (le_maxr … Hee )))
  ]
] qed.
 

let rec alpha_crumble c e n on e: fresh_var (at c e) ≤ n → 
 Σd. ∀m. (fresh_var (at c e) ≤ m) ∧ (m < n) → inb (νm) d = false ≝
 match e return λe. fresh_var (at c e) ≤ n →
     Σd. ∀m. (fresh_var (at c e) ≤ m) ∧ (m < n) → inb (νm) d = false with
 [ Epsilon ⇒ match c return λc. fresh_var (at c Epsilon) ≤ n → 
     Σd. ∀m. (fresh_var (at c Epsilon) ≤ m) ∧ (m < n) → inb (νm) d = false with
   [ CCrumble b1 e1 ⇒ λH. « (pi1 … (alpha b1 e1 n (alpha_crumble_aux1 b1 e1 n H))), ? » ]
 | Snoc e1 s ⇒ match s return λs. fresh_var (at c (Snoc e1 s)) ≤ n →
     Σd. ∀m. (fresh_var (at c (Snoc e1 s)) ≤ m) ∧ (m < n) → inb (νm) d = false with
     [ subst y b ⇒ λH. match (alpha_crumble c e1 (S n) (alpha_crumble_aux4 b c e1 n y H)) with 
   [ mk_Sig a h ⇒  « at (ssc a y (νn) (alpha_crumble_aux2 a b c e1 n y h H)) (Snoc Epsilon ([νn←b])), 
                     ? »]
   ]
 ].
 
#k #H cut (∀K. inb (νk) (at (ssc a y (νn) (K…)) (Snoc Epsilon [νn ← b]))= false) [2: #UU @UU]
  lapply h -h
  cases a #r #t #h #K'
  whd in match (ssc (CCrumble r t) y (νn) K');
  whd in match (at ? ?);
  whd in match (concat ? ?);
  >concat_e_epsilon
  whd in match (inb ? ?);
  cut (inb (νk) 〈r,t〉=false)
  [ lapply (h k) -h #h @h % [ 2: elim H #H1 #H2 /2/]
    elim H #H1 #_ @H1
  ] -h #h
  cut (neqb n k=false)
  [ elim H #_ cut (neqb n k =true ∨ neqb n k =false) // * //
    elim (neqb_iff_eq n k) #Heq #_ #Hnm lapply (Heq Hnm) -Heq #Heq >Heq
    #abs @False_ind lapply abs @le_Sn_n
  ]
  #Hf
  lapply alpha_fin1 * * * * #_ #Hbb #Hee #_ #_
  >Hbb // [ 2: lapply h normalize cases inb_b // >if_t #H @H ]
  whd in match (inb_e ? ?);
  >(Hee) // [ 2: lapply h normalize cases inb_e // >if_monotone #H @H ]
  >if_f normalize >neq_simm  >Hf  >if_f
  lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
  elim H -H #H #_
  lapply (Hdc … H) * #_ #He
  lapply (Hde … He) * #_ #Hs
  lapply (Hds … Hs) * #_ lapply (fresh_var_to_in_crumble)
  * * * * #_ #Hfvb #_ #_ #_ @Hfvb
qed.
#k * #Ha whd in match (at ? ?);
  
 

lemma fv_ss*

lemma fv_alpha:
 (∀b,e,x,n. fresh_var 〈b, e〉 ≤ n →
           fvb x 〈b,e〉 = fvb x (alpha b e n)).

#b @Environment_simple_ind2
[ #x #n normalize //
| #e * #y #b' #HI #x #n #H
  lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #_
  lapply (Hdc … H) whd in match (match ? in Crumble with [_⇒?]); * #Hb #He
  lapply (Hde … He) whd in match (match ? in Environment with [_⇒?]); * -He #He #Hs
  change with (max ? ?) in match (fresh_var ?) in HI;
  lapply (HI x (S n) (le_S … (to_max … Hb He)))
  -HI #HI -Hde -Hdc
  whd in match (fvb ? ?);
  whd in match (domb_e ? ?);
  whd in match (fvb_e ? ?);
  cut (veqb x y = true ∨ veqb x y = false) // * #Hxy >Hxy normalize
  [ >if_monotone >if_f >if_monotone >if_f
  whd in match (alpha b (Snoc e [y←b']) n);
  whd in match (match ?  in Substitution with [_⇒?]);
  check to_max

lemma nun_zo: ∀e,b,x,y,z,H2,H8,hjhj. 
 veqb x z = false → 
 (p_subst
  (aux_read_back
   (read_back_b (ssb b x (νy) H2))
   (sse e x (νy) H8))
  (psubst z (p_subst hjhj (psubst x (val_to_term (pvar νy)))))
  =p_subst (p_subst (aux_read_back (read_back_b b) e) (psubst z hjhj))
   (psubst x (val_to_term (pvar νy)))).

@Environment_simple_ind2
[ #b #x #y #z #H2 #H8 #t #Hxz >sse_epsilon
  change with (read_back_b (ssb …)) in match (aux_read_back (read_back_b (ssb …)) Epsilon);
  change with (read_back_b b) in match (aux_read_back (read_back_b b) Epsilon);
  
  normalize

   
lemma ssc_over_rb:
 (∀c.∀x,y,H. (read_back (ssc c x (νy) H)) = p_subst (read_back c) (psubst x (val_to_term (pvar νy)))) ∧
  (∀b.∀x,y,H. read_back_b (ssb b x (νy) H) = p_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) ∧
   (∀e.∀b.∀x,y,H,H1. (read_back_b (ssb b x (νy) H) = p_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) →
                 (read_back (ssc 〈b,e〉 x (νy) H1) = p_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))))) ∧
    (∀v.∀x,y,H. (read_back_v (ssv v x (νy) H)) = p_subst (read_back_v v) (psubst x (val_to_term (pvar νy)))) ∧
     (∀s.∀b.∀e.∀x,y,H,H1. (read_back (ssc 〈b,e〉 x (νy) H) = p_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))) → 
                      (read_back (ssc 〈b,Snoc e s〉 x (νy) H1) = p_subst (read_back 〈b,Snoc e s〉) (psubst x (val_to_term (pvar νy)))))).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #H @(He b x y … (Hb x y …)…) /2/
| #v #Hv whd in match (read_back_b (CValue ?)); @Hv
| #v #w #Hv #Hw #x #y #H
  whd in match (read_back_b ?);
  whd in match (read_back_b ?);
  >p_subst_distro >(Hv ) >(Hw) //
| * #z * #x #y #H
  whd in match (read_back_v (var νz));
  whd in match (ssv ? ? ? ?);
  whd in match (veqb ? ?);
  cut (neqb z x = true ∨ neqb z x = false) // * #Hzx >Hzx
  [ >if_t whd in match (read_back_v ?);
    elim (neqb_iff_eq z x) #Heq #_ lapply (Heq Hzx) -Heq #Heq destruct
    >atomic_subst //
  | >if_f >no_subst normalize //
  ]
| * #z * #b #e #Hc * #x #y #H
  whd in match (ssv ? ? ? ?);
  whd in match (veqb ? ?);
  cut (neqb z x = true ∨ neqb z x = false) // * #Hzx >Hzx
  [ >if_t whd in match (read_back_v ?);
    whd in match (read_back_v ?);
    elim (neqb_iff_eq z x) #Heq #_ lapply (Heq Hzx) -Heq #Heq destruct
    >no_subst2 //
  | >if_f whd in match (read_back_v ?);
    whd in match (read_back_v ?);
    change with (read_back (〈ssb…,sse…〉)) in match (aux_read_back (read_back_b (ssb…)) (sse…));
    lapply (Hc (νx) y ?)
    [ lapply H normalize cases inb_b normalize
      [ >if_monotone #H @H
      | cases inb_e // >if_monotone #H @H
      ]
    ]
    whd in match (ssc ? ? ? ?);
    #Hc'
    >Hc' -Hc'
    whd in match (read_back ?);
    >abstr_step_subst //
    lapply H normalize
    >neq_simm cases neqb normalize //
  ]
| #b #x #y #H #HH >ssc_step
  >sse_epsilon #HI normalize
  normalize in HI; >HI //
| #e #s #He #Hs #b #x #y #H1 #H2 #h'
  lapply (He … h')
  [ lapply H2 normalize cases inb_b normalize // cases inb_e // normalize #H @H]
  #He' @Hs [2: @He' | skip ]
| #z #b' #HI #b
  @Environment_simple_ind2
  [ #x #y #H1 #H2
    >ssc_step >ssc_step >sse_epsilon
     whd in match (read_back (CCrumble (ssb …) …));  #HI'
    change with (aux_read_back ? ?) in match (read_back ?);
    change with (p_subst ? ?) in match (read_back ?);
    cut (veqb x z = true ∨ veqb x z = false) // * #Hxz
    [ 2: >sse_step1 //
      change with (p_subst ? ?) in match (aux_read_back ? ?); 
      >HI >HI' >sse_epsilon whd in match (read_back 〈b, Epsilon〉);
      change with (p_subst … (read_back_b b) ?) in match (aux_read_back (p_subst … (read_back_b b) ?) Epsilon);
      letin t ≝ (read_back_b b)
      letin u ≝ (read_back_b b')
    | elim (veqb_true_to_eq x z) #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct
      >sse_step2
      change with (p_subst ? ?) in match (aux_read_back ? ?);
      >HI >HI' >sse_epsilon whd in match (read_back 〈b, Epsilon〉);
      change with (p_subst … (read_back_b b) ?) in match (aux_read_back (p_subst … (read_back_b b) ?) Epsilon);
      letin t ≝ (read_back_b b)
      letin u ≝ (read_back_b b')
      hrhttr
       letin t ≝ (read_back_b b')
    letin Hy ≝ (alpha_lemma2 (νy) b (Snoc e [z←b']) H2)
    letin Hj ≝ (alpha_lemma8 (νy) e z b' (alpha_lemma1 (νy) b (Snoc e [z←b']) H2))
    
  change with (aux_read_back ? ?) in match (read_back ?) in H2;
  >H2
  whd in match (read_back ?);
  >HI //
  letin mlml ≝ (aux_read_back (read_back_b b) e)
  letin hjhj ≝ (read_back_b b')

lemma ssc_over_rb:
 (∀c.∀x,y. fresh_var c ≤ y→ (read_back (ssc c x νy)) = p_subst (read_back c) (psubst x (val_to_term (pvar νy)))) ∧
  (∀b.∀x,y. fresh_var_b b ≤ y → read_back_b (ssb b x νy) = p_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) ∧
   (∀e.∀b.∀x,y. (fresh_var_b b ≤ y → read_back_b (ssb b x νy) = p_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) →
                 (fresh_var 〈b,e〉 ≤ y → read_back (ssc 〈b,e〉 x νy) = p_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))))) ∧
    (∀v.∀x,y. fresh_var_v v ≤ y → (read_back_v (ssv v x νy)) = p_subst (read_back_v v) (psubst x (val_to_term (pvar νy)))) ∧
     (∀s.∀b.∀e.∀x,y. (fresh_var 〈b,e〉 ≤ y → read_back (ssc 〈b,e〉 x νy) = p_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))) → 
                      (fresh_var 〈b,Snoc e s〉 ≤ y → read_back (ssc 〈b,Snoc e s〉 x νy) = p_subst (read_back 〈b,Snoc e s〉) (psubst x (val_to_term (pvar νy)))))).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y @(He b x y (Hb x y))
| #v #Hv whd in match (read_back_b (CValue ?)); @Hv
| #v #w #Hv #Hw #x #y whd in match (fvb_b ? ?);
  #H
  whd in match ((ssb (AppValue ? ?) ? ?));
  whd in match (read_back_b ?);
  whd in match (read_back_b ?);
  change with (max ? ? ≤?) in H;
  >p_subst_distro >(Hv … (le_maxl … H)) >(Hw … (le_maxr … H)) //
| * #z * #x #y
  whd in match (read_back_v (var νz));
  whd in match (ssv ? ? ?);
  whd in match (veqb ? ?);
  whd in match (veqb ? ?);
  cut (neqb z x = true ∨ neqb z x = false) // * #Hzx >Hzx
  [ >if_t whd in match (read_back_v ?);
    elim (neqb_iff_eq z x) #Heq #_ lapply (Heq Hzx) -Heq #Heq destruct
    >atomic_subst //
  | >if_f >no_subst normalize //
  ]
| * #z * #b #e #Hc * #x #y
  whd in match (ssv ? ? ?);
  whd in match (veqb ? ?);
  cut (neqb z x = true ∨ neqb z x = false) // * #Hzx >Hzx
  [ >if_t whd in match (read_back_v ?);
    whd in match (read_back_v ?);
    elim (neqb_iff_eq z x) #Heq #_ lapply (Heq Hzx) -Heq #Heq destruct
    >no_subst2 //
  | >if_f whd in match (read_back_v ?);
    whd in match (read_back_v ?); #H
    >abstr_step_subst
    lapply fresh_var_distr_crumble * * * * #_ #_ #_ #Hcv #_
    lapply (Hcv … H) normalize * #Hyz #Hbe -Hcv
    [ 2: cut (neqb z y = true ∨ neqb z y = false) // * #Hzy >Hzy // normalize
      elim (neqb_iff_eq z y) #Heq #_ lapply (Heq Hzy) -Heq #Heq destruct
      @False_ind @(le_Sn_n y) @Hyz
    | 3: normalize >neq_simm @Hzx
    ]
    @eq_f @eq_f2 // normalize in Hc; normalize @Hc @Hbe
  ]
| #b #x #y #H #H' normalize normalize in H; >H //
  change with (max ? ? ≤ ? ) in H';
  whd in match (fresh_var_e ?) in H';
  @(le_maxl … H')
| #e #s #He #Hs #b #x #y #h'
  lapply (He … h') #He'
  #H @Hs [2: @He' |3: @H]
  lapply fresh_var_distr_crumble * * * * #Hcf #_ #Hef #_ #_
  lapply (Hcf … H) * #Hb #He
  lapply (Hef … He) * #He #Hs
  change with (max ? ?≤?) in ⊢%;
  @to_max //
| #z #b' #HI #b #e #x #y #H1 #H2 #H3
  lapply fresh_var_distr_crumble * * * * #Hcf #_ #Hef #_ #Hsf
  lapply (Hcf … H3) * #Hb #He -Hcf
  lapply (Hef … He) * #He #Hs -Hef
  lapply (Hsf … Hs) * #Hy #Hb' -Hsf
  whd in match (ssc ? ? ?);
  change with (p_subst ? ?) in match (read_back ?);
  change with (p_subst ? ?) in match (read_back ?);
  whd in match (ssc ? ? ?) in H2;
  change with (aux_read_back ? ?) in match (read_back ?) in H2;
  >H2
  whd in match (read_back ?);
  >HI //
  letin mlml ≝ (aux_read_back (read_back_b b) e)
  letin hjhj ≝ (read_back_b b')
*)
