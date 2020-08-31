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

lemma alpha_lemma7: ∀z, e, w, b. inb_e z (Cons e [w←b])=false → (inb_b z b=false).
#z #e #w #b normalize cases inb_b // >if_monotone >if_monotone #H @H qed.

lemma alpha_lemma8: ∀z, e, w, b. inb_e z (Cons e [w←b])=false → (inb_e z e=false).
#z #e #w #b normalize cases inb_e // >if_t #H @H qed.

let rec ssc c y z on c: inb z c = false → Crumble ≝
 match c return λc. inb z c = false → Crumble with 
  [ CCrumble b e ⇒ λp. 〈ssb b y z ?, sse e y z ?〉
  ]

and ssb b y z on b: inb_b z b = false → Byte ≝
 match b return λg. inb_b z g = false → Byte with
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
 | Cons e s ⇒ match s return λs. inb_e z (Cons e s) = false → Environment with
    [ subst w b ⇒ match veqb y w with
      [ true ⇒ λp. Cons (sse e y z ?) [z←ssb b y z ?]
      |  false ⇒ λp. Cons (sse e y z ?) [w←ssb b y z ?]
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
 | Cons e s ⇒ match s with [ subst w b ⇒ match veqb y w with
                                          [ true ⇒ Cons e [w←ssb b y z]
                                          |  false ⇒ Cons (sse e y z) [w←ssb b y z]
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
 sse (Cons e [w ← b]) y z H = Cons (sse e y z ?) [w ← ssb b y z ?].
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
 sse (Cons e [y ← b]) y z H = Cons (sse e y z ?) [z ← ssb b y z ?].
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


let rec alpha0 b e n (l:nat) on l: e_size e = l → Byte×Environment ≝
 match l return λl. e_size e = l → Byte×Environment with
 [ O ⇒  match e return λe. e_size e = O → Byte×Environment with
       [ Epsilon ⇒ λp. (mk_Prod Byte Environment b Epsilon) 
       | Cons e' s ⇒ λp. ?
       ]
 | S m ⇒ match e return λe. e_size e = S m → Byte×Environment with 
   [ Epsilon ⇒ λp. ?
   | Cons e' s ⇒ λp. match s with
     [ subst y b' ⇒ let z ≝ ((alpha0 (ssb b y νn) (sse e' y νn) (S n) m) ?) in 
       mk_Prod Byte Environment (\fst z)
       (Cons (\snd  z) (subst (νn) (ssb b' y (νn))))
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

lemma alpha_aux1:  ∀b,e',s,n. (fresh_var 〈b,Cons e' s〉≤n) → (fresh_var 〈b,e'〉≤S n).
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
  (fresh_var 〈b,Cons e' [y←b']〉≤n) →
   (inb (νn) a=false).

#b #e' #a #n #y #b' #h #p @h % // 
lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #Hds
lapply (Hdc … p) * #Hb #He
lapply (Hde … He) * -He #He #Hs
change with (max ? ? ≤n)
@to_max // qed.

lemma alpha_aux4:
 ∀b, e', a, n, y, b'.
  ∀(h:(∀m:ℕ.fresh_var 〈b,e'〉≤m∧m<S n→inb (νm) a=false)).
   ∀p: (fresh_var 〈b,Cons e' [y←b']〉≤n).
   (∀m:ℕ.fresh_var 〈b,Cons e' [y←b']〉≤m∧m<n
     →inb (νm) (at (ssc a y (νn) (alpha_aux3 b e' a n y b' h p)) (Cons Epsilon [νn←b']))
    =false).

#b #e' #a #n #y #b' #h #p
#m #H cut (∀K. inb (νm) (at (ssc a y (νn) (K…)) (Cons Epsilon [νn ← b']))= false) [2: #UU @UU]
  lapply h -h
  cases a #r #t #h #K
  whd in match (ssc (CCrumble r t) y (νn) K);
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

let rec alpha (b: Byte) (e: Environment) (n: nat) on e:
 fresh_var 〈b, e〉 ≤ n → 
  Σc. ∀m. fresh_var 〈b, e〉 ≤ m ∧ m < n → inb (νm) c = false ≝ 
 match e return λe. fresh_var 〈b, e〉 ≤ n → Σc. ∀m. fresh_var 〈b, e〉 ≤ m ∧ m < n → inb (νm) c = false  with
 [ Epsilon ⇒ λp. mk_Sig … 〈b, Epsilon〉 (alpha_aux2 b n)
 | Cons e' s ⇒ match s return λs. fresh_var 〈b, Cons e' s〉 ≤ n → Σc. ∀m. fresh_var 〈b, Cons e' s〉 ≤ m ∧ m < n → inb (νm) c = false with 
   [subst y b' ⇒ λp. match alpha b e' (S n) (alpha_aux1 … (subst y b') … p) with
     [ mk_Sig a h ⇒ mk_Sig …(at (ssc (a) y (νn) (alpha_aux3 b e' a n y b' h p)) (Cons Epsilon (subst (νn) b'))) (alpha_aux4 b e' a n y b' h p) ]
   ]
 ]
.
(*  
let rec alpha (b: Byte) (e: Environment) (n: nat) on e: fresh_var 〈b, e〉 ≤ n → Crumble ≝ 
 match e return λe. fresh_var 〈b, e〉 ≤ n → Crumble  with
 [ Epsilon ⇒ λp. 〈b, Epsilon〉
 | Cons e' s ⇒ match s return λs. fresh_var 〈b, Cons e' s〉 ≤ n → Crumble with 
   [subst y b' ⇒ λp. at (ssc (alpha b e' (S n) (alpha_aux1 … (subst y b') … p)) y (νn) ?) (Cons Epsilon (subst (νn) b'))]
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
     [subst (y:Variable)   (b:Byte)⇒veqb ? ?∨domb_e ? (sse e (νx) (νn))])
   in match (domb_e (νy) (Cons (sse ? ? ?) (sss ? ? ?)));
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
  whd in match (sse (Cons ? ?) ? ?);
  whd in match (domb_e ? (Cons ? ?));
  whd in match (domb_e ? (Cons ? ?));
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
 dist_dom (Cons (Cons e s) t) = true  →  
  dist_dom (Cons (Cons e t) s) = true.

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
  (dist_dom (Cons e [z←b])=true) →
   veqb y z=false →
    veqb (νn) z=false →
     (domb_e z (sse e y (νn) H)=false).

@Environment_simple_ind2
[ //
| #e * * #w #b' #HI * #y #n * #z #b #H #Hddom
  cut (dist_dom (Cons e [νz←b])=true)
  [ >(dist_dom_conservative … [νw ← b']) // >dist_dom_switch // ]
  #Hd lapply Hddom -Hddom
 whd in match (dist_dom ?);
  whd in match (match ? in Substitution with [_⇒?]);
  #Hddom
  cut (domb_e (νz) (Cons e [νw ← b'])=false)
  [ lapply Hddom cases domb_e normalize //]
  #Hdomb
  cut (dist_dom (Cons e [νw←b'])=true)
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
      «at (ssc a y (νn) (alpha_aux3 b e' a n y b' h H)) (Cons Epsilon [νn←b']),
      alpha_aux4 b e' a n y b' h H»]);
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
  whd in match (alpha b (Cons e [νy←b']) n H);
  cases alpha * #b'' #e' #HH
  whd in match ( match «〈b'',e'〉,?»
    in Sig
    with 
   [mk_Sig a h⇒
    «at (ssc a (νy) (νn) (alpha_aux3 b e a n (νy) b' h H)) (Cons Epsilon [νn←b']),
    alpha_aux4 b e a n (νy) b' h H»]);
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
  whd in match (concat ? (Cons ? ?));
  whd in match (match ? in Crumble with [_ ⇒?]);
  whd in match (match ? in Crumble with [_ ⇒?]);
  whd in match (alpha b (Cons ? ?) ? ?);
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
   [mk_Sig a h⇒ «at (ssc a (νy) (νn) (alpha_aux3 b (concat ??) a n (νy) b' h H))(Cons Epsilon [νn←b']),
       alpha_aux4 b (concat ??) a n (νy) b' h H»]);
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
  | whd in match (concat ? ?); whd in match (domb_e ? (Cons ? ?) ); >did_aux
    [ 2: lapply (Hb n) cases domb_e // #H @False_ind @(le_Sn_n n) @H @refl
    | 3: lapply (Hb y) cases domb_e // #H @False_ind @(le_Sn_n n)
         lapply (le_S … (H (refl …))) -H #H @(transitive_le … H Hy)
    | whd in match (veqb ? ?); >Hzn >if_f #H lapply (Hb … H) -H #H  lapply (le_S … H) /2/
    ]
  ]
] qed.
(*
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
  whd in match (alpha b (Cons e [y←b']) n);
  whd in match (match ?  in Substitution with [_⇒?]);
  check to_max

lemma nun_zo: ∀e,b,x,y,z,H2,H8,hjhj. 
 veqb x z = false → 
 (pif_subst
  (aux_read_back
   (read_back_b (ssb b x (νy) H2))
   (sse e x (νy) H8))
  (psubst z (pif_subst hjhj (psubst x (val_to_term (pvar νy)))))
  =pif_subst (pif_subst (aux_read_back (read_back_b b) e) (psubst z hjhj))
   (psubst x (val_to_term (pvar νy)))).

@Environment_simple_ind2
[ #b #x #y #z #H2 #H8 #t #Hxz >sse_epsilon
  change with (read_back_b (ssb …)) in match (aux_read_back (read_back_b (ssb …)) Epsilon);
  change with (read_back_b b) in match (aux_read_back (read_back_b b) Epsilon);
  
  normalize

   
lemma ssc_over_rb:
 (∀c.∀x,y,H. (read_back (ssc c x (νy) H)) = pif_subst (read_back c) (psubst x (val_to_term (pvar νy)))) ∧
  (∀b.∀x,y,H. read_back_b (ssb b x (νy) H) = pif_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) ∧
   (∀e.∀b.∀x,y,H,H1. (read_back_b (ssb b x (νy) H) = pif_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) →
                 (read_back (ssc 〈b,e〉 x (νy) H1) = pif_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))))) ∧
    (∀v.∀x,y,H. (read_back_v (ssv v x (νy) H)) = pif_subst (read_back_v v) (psubst x (val_to_term (pvar νy)))) ∧
     (∀s.∀b.∀e.∀x,y,H,H1. (read_back (ssc 〈b,e〉 x (νy) H) = pif_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))) → 
                      (read_back (ssc 〈b,Cons e s〉 x (νy) H1) = pif_subst (read_back 〈b,Cons e s〉) (psubst x (val_to_term (pvar νy)))))).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #H @(He b x y … (Hb x y …)…) /2/
| #v #Hv whd in match (read_back_b (CValue ?)); @Hv
| #v #w #Hv #Hw #x #y #H
  whd in match (read_back_b ?);
  whd in match (read_back_b ?);
  >pif_subst_distro >(Hv ) >(Hw) //
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
    change with (pif_subst ? ?) in match (read_back ?);
    cut (veqb x z = true ∨ veqb x z = false) // * #Hxz
    [ 2: >sse_step1 //
      change with (pif_subst ? ?) in match (aux_read_back ? ?); 
      >HI >HI' >sse_epsilon whd in match (read_back 〈b, Epsilon〉);
      change with (pif_subst … (read_back_b b) ?) in match (aux_read_back (pif_subst … (read_back_b b) ?) Epsilon);
      letin t ≝ (read_back_b b)
      letin u ≝ (read_back_b b')
    | elim (veqb_true_to_eq x z) #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct
      >sse_step2
      change with (pif_subst ? ?) in match (aux_read_back ? ?);
      >HI >HI' >sse_epsilon whd in match (read_back 〈b, Epsilon〉);
      change with (pif_subst … (read_back_b b) ?) in match (aux_read_back (pif_subst … (read_back_b b) ?) Epsilon);
      letin t ≝ (read_back_b b)
      letin u ≝ (read_back_b b')
      hrhttr
       letin t ≝ (read_back_b b')
    letin Hy ≝ (alpha_lemma2 (νy) b (Cons e [z←b']) H2)
    letin Hj ≝ (alpha_lemma8 (νy) e z b' (alpha_lemma1 (νy) b (Cons e [z←b']) H2))
    
  change with (aux_read_back ? ?) in match (read_back ?) in H2;
  >H2
  whd in match (read_back ?);
  >HI //
  letin mlml ≝ (aux_read_back (read_back_b b) e)
  letin hjhj ≝ (read_back_b b')

lemma ssc_over_rb:
 (∀c.∀x,y. fresh_var c ≤ y→ (read_back (ssc c x νy)) = pif_subst (read_back c) (psubst x (val_to_term (pvar νy)))) ∧
  (∀b.∀x,y. fresh_var_b b ≤ y → read_back_b (ssb b x νy) = pif_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) ∧
   (∀e.∀b.∀x,y. (fresh_var_b b ≤ y → read_back_b (ssb b x νy) = pif_subst (read_back_b b) (psubst x (val_to_term (pvar νy)))) →
                 (fresh_var 〈b,e〉 ≤ y → read_back (ssc 〈b,e〉 x νy) = pif_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))))) ∧
    (∀v.∀x,y. fresh_var_v v ≤ y → (read_back_v (ssv v x νy)) = pif_subst (read_back_v v) (psubst x (val_to_term (pvar νy)))) ∧
     (∀s.∀b.∀e.∀x,y. (fresh_var 〈b,e〉 ≤ y → read_back (ssc 〈b,e〉 x νy) = pif_subst (read_back 〈b,e〉) (psubst x (val_to_term (pvar νy))) → 
                      (fresh_var 〈b,Cons e s〉 ≤ y → read_back (ssc 〈b,Cons e s〉 x νy) = pif_subst (read_back 〈b,Cons e s〉) (psubst x (val_to_term (pvar νy)))))).

@Crumble_mutual_ind
[ #b #e #Hb #He #x #y @(He b x y (Hb x y))
| #v #Hv whd in match (read_back_b (CValue ?)); @Hv
| #v #w #Hv #Hw #x #y whd in match (fvb_b ? ?);
  #H
  whd in match ((ssb (AppValue ? ?) ? ?));
  whd in match (read_back_b ?);
  whd in match (read_back_b ?);
  change with (max ? ? ≤?) in H;
  >pif_subst_distro >(Hv … (le_maxl … H)) >(Hw … (le_maxr … H)) //
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
  change with (pif_subst ? ?) in match (read_back ?);
  change with (pif_subst ? ?) in match (read_back ?);
  whd in match (ssc ? ? ?) in H2;
  change with (aux_read_back ? ?) in match (read_back ?) in H2;
  >H2
  whd in match (read_back ?);
  >HI //
  letin mlml ≝ (aux_read_back (read_back_b b) e)
  letin hjhj ≝ (read_back_b b')
*)
lemma alpha_same_rb: 
 ∀b,e,n,H. read_back 〈b, e〉= read_back (pi1 Crumble ? (alpha b e n H)).
#b
@Environment_simple_ind2
[ #n normalize //
| #e * #y #b' #H #n
  whd in match (alpha …);
  lapply fresh_var_distr_crumble * * * * #Hdc #_ #Hde #_ #_ #Hfv
  lapply (Hdc … Hfv) * #Hfvb #Hfve
  lapply (Hde … Hfve) * -Hfve #Hfve #Hfvs
  lapply (H (S n) (le_S …?)) [ @to_max // ]
  #Hd
  change with (pif_subst (aux_read_back ? ?) (psubst ? ?)) in match (read_back ?);
  change with ( (aux_read_back ? ?)) in match (read_back ?) in Hd;
  >Hd
  whd in match (alpha b (Cons e [y←b']) n Hfv);
  (*qui sicuramente erdo roba su alpha*)
  cases alpha * #r #t #rt_prop
  whd in match (match «CCrumble r t,rt_prop» in Sig 
    with [ mk_Sig a h ⇒ «at (ssc a y (νn) (alpha_aux3 b e a n y b' h Hfv))(Cons Epsilon [νn←b']),
     alpha_aux4 b e a n y b' h Hfv»]);
  whd in match (ssc 〈r,t〉 y (νn) (alpha_aux3 b e 〈r,t〉 n y b' rt_prop Hfv));
  whd in match (at ? ?);
  whd in match (concat ? ?);
  >concat_e_epsilon
  change with (pif_subst (aux_read_back ? ?) (psubst ? ?)) in match
    (read_back 〈ssb r y (νn) ?, …〉);
  change with (read_back 〈ssb r y (νn) ?, sse t y (νn) ?〉) in match 
    (aux_read_back (read_back_b  (ssb …)) (sse …));
  change with (ssc y νn 〈r, t〉 ?)
    in match (〈ssb r y (νn) ? , sse t y (νn) ?〉);
  whd in match (ssc 〈r, t〉 y (νn));
  whd in match (match ? in Crumble with
    [_⇒?] );
  whd in match (concat ? ?);
  >concat_e_epsilon
  change with (pif_subst (aux_read_back ? ?) (psubst ? ?)) in match (read_back ?);
  change with (pif_subst (read_back (ssc 〈r, t〉 y νn)) ?) in ⊢ (? ? ? %);
  change with (read_back 〈r,t〉) in match (aux_read_back (read_back_b r) t);
  (*non sembra che si siano perse informazioni importantissime ma servono due lemmi ad occhio:
    - commutazione di ss* con sostituzione di variabili rispetto a read_back
    - lemma sull'accorpamento di sostituzioni da [x<-y][y<-t] → [x<-t]. 
   *)
   
  @eq_f
  
  change with (Cons e0 [νn←b']) in match (concat e0 (Cons Epsilon [νn←b']));
 >concat_epsilon_e
  whd in match (read_back 〈b,Cons e [y←b']〉);
  >concat_epsilon_e whd in match (concat ? (Cons Epsilon ?));  
       