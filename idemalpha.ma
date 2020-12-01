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

include "other4dot5dot5.ma".

let rec alpha2_e  (e: Environment) (n: nat) on e:
 fresh_var_e e ≤ n → 
  Σd. ∀m. fresh_var_e e ≤ m ∧ m < n → inb_e (νm) d = false ≝ 
 match e return λe. fresh_var_e e ≤ n → Σd. ∀m. fresh_var_e e ≤ m ∧ m < n → inb_e (νm) d = false  with
 [ Epsilon ⇒ λp. mk_Sig … Epsilon ?
 | Snoc e' s ⇒ match s return λs. fresh_var_e (Snoc e' s) ≤ n → Σd. ∀m. fresh_var_e (Snoc e' s) ≤ m ∧ m < n → inb_e (νm) d = false with 
   [subst y b' ⇒ λp. mk_Sig … (Snoc (sse (pi1 … (alpha2_e e' (S n) (alpha_e_aux3 … p))) y (νn) (alpha_e_aux2 … p (pi2 … (alpha2_e e' (S n) (alpha_e_aux3 … p))))) (subst (νn) b')) (alpha_e_aux4 alpha_e … p (pi2 … (alpha2_e e' (S n) (alpha_e_aux3 … p)))) ]
 ].
 @(alpha_e_aux1 … n) qed.
 
lemma alphae_eq: ∀e, n, H. alpha2_e e n H = alpha_e e n H.
@Environment_simple_ind2
[ //
| #e * #y #b #HI #n #H whd in match (alpha2_e ? ? ?);
 whd in match (alpha_e ? ? ?);
 <(HI (S n) (alpha_e_aux3 n e y b H))
 cases (alpha2_e e (S n) ?) //
] qed.

lemma ss_xc: 
∀a, b, c, d.veqb a c = false → veqb a d = false → veqb c b = false →
(
(∀z, H1, H2, H3, H4.
ssc (ssc z a b H1) c d H2 = ssc (ssc z c d H3) a b H4) ∧

(∀z,  H1, H2, H3, H4. 
ssb (ssb z a b H1) c d H2 = ssb (ssb z c d H3) a b H4) ∧

(∀z,  H1, H2, H3, H4. 
sse (sse z a b H1) c d H2 = sse (sse z c d H3) a b H4) ∧

(∀z,  H1, H2, H3, H4. 
ssv (ssv z a b H1) c d H2 = ssv (ssv z c d H3) a b H4) ∧

(∀z,  H1, H2, H3, H4. 
sss (sss z a b H1) c d H2 = sss (sss z c d H3) a b H4)).
#a #b #c #d #P1 #P2 #P3
@Crumble_mutual_ind
[ #b #e #Hb #He #H1 #H2 #H3 #H4 lapply H2 lapply H4
  whd in match (ssc (CCrumble ? ?) a ? ?);
  whd in match (ssc (CCrumble ? ?) c ? ?);
  cut (domb_e c e = true ∨ domb_e c e = false) // * #Hdce >Hdce
  cut (domb_e a e = true ∨ domb_e a e = false) // * #Hdae >Hdae
  [ >if_t >if_t #H2 #H4 whd in match (ssc ? ? ? ?);
    >dom_sse >Hdce >if_t whd in match (ssc ? ? ? ?);
    >dom_sse >Hdae >if_t >He //
  | >if_t >if_f -H2 -H4 #H4 #H2 whd in match (ssc ? ? ? ?);
    >dom_sse >Hdce >if_t whd in match (ssc ? ? ? ?);
    >dom_sse >Hdae >if_f /2/
  | >if_f >if_t -H2 -H4 #H4 #H2 whd in match (ssc ? ? ? ?);
    >dom_sse >Hdce >if_f whd in match (ssc ? ? ? ?);
    >dom_sse >Hdae >if_t /2/
  | >if_f >if_f -H4 #H4 #H2 whd in match (ssc ? ? ? ?);
    >dom_sse >Hdce >if_f whd in match (ssc ? ? ? ?);
    >dom_sse >Hdae >if_f /2/
  ]
| #v #HI #H1 #H2 #H3 #H4 normalize @eq_f @HI
| #v #w #Hv #Hw #H1 #H2 #H3 #H4 normalize >Hv //
| #x #H1 #H2 #H3 #H4 lapply H2 lapply H4 normalize
  cut (veqb x a = true ∨ veqb x a = false) // * #Hxa >Hxa
  [ >if_t -H4 -H2 elim (veqb_true_to_eq x a) #Heq #_
    lapply (Heq Hxa) -Heq #Heq destruct >P1 >if_f #H4 #H2
    normalize >veqb_comm >P3 >if_f >veqb_true >if_t //
  | >if_f -H4 -H2 whd in match (ssv ? ? ? ?); cases (veqb x c)
    [ >if_t  #H4 #H2 normalize >veqb_comm >P2 >if_f //
    | >if_f #H4 #H2 normalize >Hxa >if_f //
    | // | // ]
  ]
| #x #z #HI #H1 #H2 #H3 #H4
  lapply H2
  whd in match (ssv (lambda ? ?) ? ? ?);
  cut (veqb x a = true ∨ veqb x a = false) // * #Hxa >Hxa
  [  elim (veqb_true_to_eq x a) #Heq #_
    lapply (Heq Hxa) -Heq #Heq destruct >if_t
    lapply H4 normalize  >P1 >if_f #H4 #H2 normalize >veqb_true >if_t
    normalize //
  | >if_f lapply H4 normalize cases (veqb x c)
    [ normalize -H4 #H4 -H2 #H2 >Hxa >if_f normalize //
    | >if_f >if_f normalize -H4 #H4 -H2 #H2 >Hxa >if_f normalize >HI //
    ]
  ]
| //
| #e * #z #r #He #Hs #H1 #H2 #H3 #H4 lapply H2
  whd in match (sse (Snoc ? ?) ? ? ?);
  cut (veqb a z = true ∨ veqb a z = false) // * #Hxa >Hxa
  [  elim (veqb_true_to_eq a z) #Heq #_
    lapply (Heq Hxa) -Heq #Heq destruct >if_t
    lapply H4 normalize >(veqb_simm c z)  >P1 >if_f #H4 #H2 normalize >veqb_true >if_t
    normalize @eq_f2 // lapply (Hs ? ? ? ?) 
    [ 5: #HH @HH]
    [ 2: elim (orb_false … H3) //
    | 4: elim (orb_false … H1) //
    | lapply H4 normalize cases inb_e // >if_t #abs destruct
    | lapply H2 normalize cases inb_e // >if_t #abs destruct
    ]
  | >if_f lapply H4 normalize cases (veqb c z)
    [ normalize -H4 #H4 -H2 #H2 >Hxa >if_f normalize @eq_f2 // @Hs
    [ 1: elim (orb_false … H1) //
    | 3: elim (orb_false … H3) //
    | lapply H2 normalize cases inb_e // >if_t #abs destruct
    | lapply H4 normalize cases inb_e // >if_t #abs destruct
    ]
    | >if_f >if_f normalize -H4 #H4 -H2 #H2 >Hxa >if_f normalize @eq_f2
      [ >He // ] @Hs
    [ 1: elim (orb_false … H1) //
    | 3: elim (orb_false … H3) //
    | lapply H2 normalize cases inb_e // >if_t #abs destruct
    | lapply H4 normalize cases inb_e // >if_t #abs destruct
    ]
    ]
  ]

| #x #b #HI #H1 #H2 #H3 #H4 normalize >HI //
] qed.
(*
lemma inbf_decode: 
(∀c, x, y, z, H. (inb x (ssc c y z H) = ((inb x c ∧ ¬veqb x z) ∨ (¬(inb x c) ∧ veqb x z)))) ∧
(∀b, x, y, z, H. (inb_b x (ssb b y z H) = ((inb_b x b ∧ ¬veqb x z) ∨ (¬(inb_b x b) ∧ veqb x z)))) ∧
(∀e, x, y, z, H. (inb_e x (sse e y z H) = ((inb_e x e ∧ ¬veqb x z) ∨ (¬(inb_e x e) ∧ veqb x z)))) ∧
(∀v, x, y, z, H. (inb_v x (ssv v y z H) = ((inb_v x v ∧ ¬veqb x z) ∨ (¬(inb_v x v) ∧ veqb x z)))) ∧
(∀s, x, y, z, H. (inb_s x (sss s y z H) = ((inb_s x s ∧ ¬veqb x z) ∨ (¬(inb_s x s) ∧ veqb x z))))
.
@Crumble_mutual_ind
[ #b #e #Hb #He #x #y #z #H
  whd in match (ssc ? ? ? ?);
  cut (domb_e y e = true ∨ domb_e y e = false) // * #Hdy >Hdy
  [ >if_t whd in match (inb ? ?); >He normalize cases inb_b // >if_t >if_t >if_t
    >if_f >if_then_true_else_false 
*)

lemma inalphae: ∀e, n, H, x. inb_e (νx) e = false → x < n → 
inb_e (νx) (pi1 … (alpha_e e n H)) = false.
@Environment_simple_ind2
[ //]
#e * #w #d #HI #n #H #x #K #J whd in match (alpha_e ? ? ?);
lapply (HI (S n) ? x ? ?)[ @le_S // | elim (orb_false … K) // | @alpha_e_aux3 // ]
cases alpha_e #f #h whd in match (match ? in Sig with [_⇒?]);
whd in match (inb_e ? (Snoc ? ?));
lapply alpha_fin1 * * * * #_ #_ #Hee #_ #_ #HH >Hee // [ >if_f lapply K
 whd in match (inb_e ? ?); whd in match (inb_s ? ?); whd in match (inb_s ? ?);
 cases inb_b [ >if_monotone >if_monotone >if_monotone // ] >if_then_true_else_false
 >if_then_true_else_false #_ cut (neqb x n = true ∨ neqb x n = false) // * //
 #Htt elim (neqb_iff_eq x n) #Heq #_ lapply (Heq Htt) -Heq #Heq destruct @False_ind
 lapply J @le_Sn_n ]cut (neqb x n = true ∨ neqb x n = false) // * //
 #Htt elim (neqb_iff_eq x n) #Heq #_ lapply (Heq Htt) -Heq #Heq destruct @False_ind
 lapply J @le_Sn_n qed.
 
lemma inalpha2e: ∀e, n, H, x. inb_e (νx) e = false → x < n → 
inb_e (νx) (pi1 … (alpha2_e e n H)) = false.
#e #d #HI #n #H #x >alphae_eq @inalphae // qed.

lemma alpha_e_comm: ∀e, y, z, m, H1, H2, H3, H4. domb_e (νy) e = false → 
y < m → inb_e (νz) e = false → z<m → 
pi1 …(alpha2_e (sse e (νy) (νz) H1) m H2) = sse (pi1 … (alpha2_e e m H3)) (νy) (νz) H4.
@Environment_simple_ind2 [//]
#e * #w #b #HI #y #z #m #H1 #H2 #H3 #H4 #Hd #Hym #Hfv #Hzm lapply H2
whd in match (sse ? ? ? ?);
cut (veqb (νy) w = false) [ lapply Hd change with (orb ? ?) in match (domb_e ? ?);
  cases veqb // >if_t // normalize // ] #Hf >Hf
>if_f #H2 lapply H4 whd in match (alpha2_e ? ? ?); whd in match (alpha2_e (Snoc ? ?) ? ?);
#H4
whd in match (sse (Snoc ? ?) ? ? ?);
cut (neqb y m = false)
[ cut (neqb y m = true ∨ neqb y m = false) // * //
  elim (neqb_iff_eq y m) #Heq #_ #HJ lapply (Heq HJ) -Heq -HJ #Heq -H2 destruct
   @False_ind lapply Hym @le_Sn_n ]
 #Hym whd in match (veqb ? ?); >Hym >if_f whd in ⊢(? ? ? %); @eq_f2 //
 generalize in match (alpha_e_aux2 ? ? ? ? ? ? ?); >HI
[ 7: @(alpha_e_aux3 m e w b H3) ]
[ 3: elim (orb_false … Hfv) //]
[ 4: lapply Hd normalize cases domb_e // >if_monotone // ]
[ 2: -Hym @(le_S … Hzm) ]
[ 2:-Hym  @(le_S … Hym) ]
[ 2: @(inalpha2e e (S m) (alpha_e_aux3 m e w b H3) z ? ?)
  [ 2: @le_S // | lapply Hfv normalize cases inb_e // >if_t //] ]
  
  lapply H4 -H4 -H2 -H2 generalize in match (inalpha2e ? ? ? ? ? ?);
  cases (alpha2_e e (S m) (alpha_e_aux3 m e w b H3)) #E #He
  whd in match (match ? in Sig with [_⇒?]);
  lapply (ss_xc (νy) (νz) w (νm) ? ? ?)
  [ 4: * * * * #_ #_ #He #_ #_  #J #K #L @He ]
  [ lapply Hfv cases w #nw whd in match (neqb ? ?);
    cut (neqb nw z=true ∨ neqb nw z=false) // * //
    #Htf elim (neqb_iff_eq nw z) #Heq lapply (Heq Htf) -Heq #Heq destruct #_
    #HH lapply HH normalize >neqb_refl >if_t >if_monotone //
  | //
  | //
  ]
qed.

(*
lemma alpha_e_comm: ∀e, y, z, m, H1, H2, H3, H4. domb_e (νy) e = false → 
y < m → fresh_var_e e ≤ z → z<m → 
pi1 …(alpha2_e (sse e (νy) (νz) H1) m H2) = sse (pi1 … (alpha2_e e m H3)) (νy) (νz) H4.
@Environment_simple_ind2 [//]
#e * #w #b #HI #y #z #m #H1 #H2 #H3 #H4 #Hd #Hym #Hfv #Hzm lapply H2
whd in match (sse ? ? ? ?);
cut (veqb (νy) w = false) [ lapply Hd change with (orb ? ?) in match (domb_e ? ?);
  cases veqb // >if_t // normalize // ] #Hf >Hf
>if_f #H2 lapply H4 whd in match (alpha2_e ? ? ?); whd in match (alpha2_e (Snoc ? ?) ? ?);
#H4
whd in match (sse (Snoc ? ?) ? ? ?);
cut (neqb y m = false)
[ cut (neqb y m = true ∨ neqb y m = false) // * //
  elim (neqb_iff_eq y m) #Heq #_ #HJ lapply (Heq HJ) -Heq -HJ #Heq -H2 destruct
   @False_ind lapply Hym @le_Sn_n ]
 #Hym whd in match (veqb ? ?); >Hym >if_f whd in ⊢(? ? ? %); @eq_f2 //
 generalize in match (alpha_e_aux2 ? ? ? ? ? ? ?); >HI
[ 7: @(alpha_e_aux3 m e w b H3) ]
[ 3: @(le_maxl … Hfv)]
[ 4: lapply Hd normalize cases domb_e // >if_monotone // ]
[ 2: -Hym @(le_S … Hzm) ]
[ 2:-Hym  @(le_S … Hym) ]
[ 2: generalize in match (alpha2_e ? ? ?); * #r #t @t %
  [ @(le_maxl … Hfv) | @(le_S … Hzm) ] ] lapply H4 -H4 -H2 -H2
  cases (alpha2_e e (S m) (alpha_e_aux3 m e w b H3)) #E #He
  whd in match (match ? in Sig with [_⇒?]);
  lapply (ss_xc (νy) (νz) w (νm) ? ? ?)
  [ 4: * * * * #_ #_ #He #_ #_ #J #K @He ]
  [ lapply Hfv cases w #nw whd in match (neqb ? ?);
    cut (neqb nw z=true ∨ neqb nw z=false) // * //
    #Htf elim (neqb_iff_eq nw z) #Heq lapply (Heq Htf) -Heq #Heq destruct #_
    #HH @False_ind lapply (le_maxl …(le_maxr … HH)) @le_Sn_n
  | //
  | //
  ]
qed.
*)
lemma to_sse:∀e, e', x, x' , y , y', H, H'.
e=e' → x = x' → y = y' → sse e x y H = sse e' x' y' H'.
#H20 #H21 #H22 #H23 #H24 #H25 #H26 #H27 #H28 #H29 #H30 destruct // qed.


lemma ss_fv_decrease:
(∀c, x, y, n, H. y < n → fresh_var c ≤ n → fresh_var (ssc c x (νy) H)≤ n)∧
(∀b, x, y, n, H. y < n → fresh_var_b b ≤ n → fresh_var_b (ssb b x (νy) H)≤ n)∧
(∀e, x, y, n, H. y < n → fresh_var_e e ≤ n → fresh_var_e (sse e x (νy) H)≤ n)∧
(∀v, x, y, n, H. y < n → fresh_var_v v ≤ n → fresh_var_v (ssv v x (νy) H)≤ n)∧
(∀s, x, y, n, H. y < n → fresh_var_s s ≤ n → fresh_var_s (sss s x (νy) H)≤ n).
@Crumble_mutual_ind
[ #b #e #H1 #H2 #x #y #n #H #K #HK whd in match (ssc ? ? ? ?);
  change with (max ? ?) in match (fresh_var ?) in HK; cases domb_e
  [ >if_t @to_max  change with (max ? ?) in match (fresh_var ?) in HK;
    [ @(le_maxl … HK) | @(H2 … n) // @(le_maxr … HK) ]
  | >if_f @to_max [ @(H1 … n) // @(le_maxl … HK) ]
    @(H2 … n) // @(le_maxr … HK) ]
| #v #HI #x #y #n #H #H1 #H2 normalize @(HI … n) //
| #v #w #Hv #Hw #x #y #n #H #H1 #H2 whd in match (ssb ? ? ? ?);
  change with (max ? ?) in match (fresh_var_b ?);
  change with (max ? ?) in match (fresh_var_b ?); @to_max
  [ @(Hv … n) // change with (max ? ?) in match (fresh_var_b ?) in H2;
    @(le_maxl … H2)
  | @(Hw … n) // change with (max ? ?) in match (fresh_var_b ?) in H2;
    @(le_maxr … H2)
  ]
| #z #x #y #n #H #H1 #H2 whd in match (ssv ? ? ? ?); cases veqb
  [ >if_t normalize @H1
  | >if_f //
  ]
| * #z #c #HI #x #y #n #H1 #H2 #H3 whd in match (ssv ? ? ? ?); cases veqb
  [ >if_t //
  | >if_f whd in ⊢ (? (? %) ?); change with (max (S ?) ?) in match (fresh_var_v ?);
    @to_max [ 2: @HI // @(le_maxr … H3)] @(le_maxl … H3)
  ]
| //
| #e * * #z #b #He #Hs #x #y #n #H1 #H2 #H3 whd in match (sse ? ? ? ?);
  cases veqb
  [ >if_t whd in ⊢ (? (? %) ?); change with (max ? ?) in match (fresh_var_e ?);
    @to_max [ @(le_maxl … H3) | @Hs // [ elim (orb_false … H1) // ]
    @(le_maxr … H3) ]
  | >if_f  whd in ⊢ (? (? %) ?); change with (max ? ?) in match (fresh_var_e ?);
    @to_max [ @He // @(le_maxl … H3) ] @Hs // [ elim (orb_false … H1) // ]
    @(le_maxr … H3)
  ]
| * #z #b #HI #x #y #n #H1 #H2 #H3
  change with (max ? ?) in match (fresh_var_s ?); @to_max
  [ @(le_maxl … H3)
  | @HI // @(le_maxr … H3)
  ]
] qed.

lemma inb_alpha_strong: ∀e, n, H, x. (inb_e (νx) e) = false →  x < n → inb_e (νx) (pi1 … (alpha_e … e n H)) = false.
@Environment_simple_ind2
[//]
#e * * #z #w #HI #n #H #x #H1 #H2 whd in match (alpha_e ? ? ?);
lapply (HI (S n) (alpha_e_aux3 n e (νz) w H) x ? (le_S … H2))
[ elim (orb_false … H1) // ] cases alpha_e #E #H
  whd in match (match ? in Sig with [_⇒?]);
  lapply alpha_fin1 * * * * #_ #_ #He #_ #_ #HII
  whd in match (inb_e ? ?);
  elim (orb_false … H1) #_
  whd in match (inb_s ? ?); whd in match (inb_s ? ?);
  whd in match (veqb ? ?); whd in match (veqb ? ?);
  cut (neqb x n = true ∨ neqb x n = false) // * #Hxn
  [ elim (neqb_iff_eq x n) #Heq lapply (Heq Hxn) -Heq #Heq destruct #_
    @False_ind lapply H2 @le_Sn_n ] >Hxn >if_f
  cases neqb [ >if_t #abs destruct] >if_f #Hg >Hg -Hg 
   >if_then_true_else_false @He //
qed.

lemma inb_alpha2_strong: ∀e, n, H, x. (inb_e (νx) e) = false →  x < n → inb_e (νx) (pi1 … (alpha2_e … e n H)) = false.
#e #n #H #x #HJ  #df >alphae_eq /2/ qed.

(*
lemma ss_fv_decrease2:
(∀c, x, y, H. fvb x c = true →  fresh_var (ssc c x (νy) H) = max (fresh_var c) (S y))∧
(∀b, x, y, H. fvb_b x b = true → fresh_var_b (ssb b x (νy) H) = max (fresh_var_b b) (S y))∧
(∀e, x, y, H. fvb_e x e = true → fresh_var_e (sse e x (νy) H) = max (fresh_var_e e) (S y))∧
(∀v, x, y, H. fvb_v x v = true → fresh_var_v (ssv v x (νy) H) = max (fresh_var_v v) (S y))∧
(∀s, x, y, H. fvb_s x s = true → fresh_var_s (sss s x (νy) H) = max (fresh_var_s s) (S y)).
@Crumble_mutual_ind
[ #b #e #H1 #H2 #x #y #H #Ha whd in match (ssc ? ? ? ?);
  lapply Ha whd in match (fvb ? ?);
  cases domb_e
  [ >if_t change with (max ? ?) in match (fresh_var ?);
    whd in match (andb ? false); >if_monotone >if_f #He >H2
    change with (max ? ?) in match (fresh_var ?); /2/
  | >if_f whd in match (andb ? true); >if_then_true_else_false
   cut (fvb_e x e = true ∨fvb_e x e = false) // * #Hfe
   cut (fvb_b x b = true ∨ fvb_b x b = false) // * #Hfb
    [ >Hfe >Hfb
      change with (max ? ?) in match (fresh_var ?); #_ >H2 // >(H1 x y) //
      change with (max ? ?) in match (fresh_var ?); //
    | lapply ssc_fv * * * * #_ #Hb #_ #_ #_ >Hb // #_
      change with (max ? ?) in match (fresh_var ?); >H2 //
      change with (max ? ?) in match (fresh_var ?); /2/
    | lapply ssc_fv * * * * #_ #_ #He #_ #_ >He // #_
      change with (max ? ?) in match (fresh_var ?); >H1 //
      change with (max ? ?) in match (fresh_var ?); /2/
    | >Hfe >Hfb normalize #abs destruct
    ]
  ]
| #v #HI #x #y #H #K whd in match (fresh_var_b ?); @(HI) lapply K normalize //
| #v #w #Hv #Hw #x #y #H whd in match (ssb ? ? ? ?);
  change with (max ? ?) in match (fresh_var_b ?);
  change with (max ? ?) in match (fresh_var_b ?);
  lapply ssc_fv * * * * #_ #_ #_ #HV #_ #K
  cut (fvb_v x v = true ∨ fvb_v x v = false) // *
  cut (fvb_v x w = true ∨ fvb_v x w = false) // * #Ha #Hb
  [ >Hv // >Hw //
  | >Hv // >HV //
  | >Hw // >HV //
  | lapply K normalize >Ha >Hb normalize #abs destruct
  ] /2/
| * #z * #x #y #H whd in match (ssv ? ? ? ?); normalize >neq_simm #HA >HA >if_t
| * #z #c #HI #x #y #n #H1 #H2 #H3 whd in match (ssv ? ? ? ?); cases veqb
  [ >if_t //
  | >if_f whd in ⊢ (? (? %) ?); change with (max (S ?) ?) in match (fresh_var_v ?);
    @to_max [ 2: @HI // @(le_maxr … H3)] @(le_maxl … H3)
  ]
| //
| #e * * #z #b #He #Hs #x #y #n #H1 #H2 #H3 whd in match (sse ? ? ? ?);
  cases veqb
  [ >if_t whd in ⊢ (? (? %) ?); change with (max ? ?) in match (fresh_var_e ?);
    @to_max [ @(le_maxl … H3) | @Hs // [ elim (orb_false … H1) // ]
    @(le_maxr … H3) ]
  | >if_f  whd in ⊢ (? (? %) ?); change with (max ? ?) in match (fresh_var_e ?);
    @to_max [ @He // @(le_maxl … H3) ] @Hs // [ elim (orb_false … H1) // ]
    @(le_maxr … H3)
  ]
| * #z #b #HI #x #y #n #H1 #H2 #H3
  change with (max ? ?) in match (fresh_var_s ?); @to_max
  [ @(le_maxl … H3)
  | @HI // @(le_maxr … H3)
  ]
] qed.


lemma alphae_fresh_var: ∀e, n, H. fresh_var_e (pi1 … (alpha_e e n H)) = fresh_var_e e+e_len e.
@Environment_simple_ind2
[ #n #H normalize //
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






lemma this_lemma: (fresh_var_e (pi1 …  (alpha2_e e (S n) Hc)) ≤m) →  (fresh_var_e (pi1 …  (alpha2_e e (S n) Hc)) ≤S m)

*)

lemma alpha_e_idem: ∀e, n, m, H1, H2, H3. m ≥n + e_len e →
 (pi1 … (alpha2_e (pi1 … (alpha2_e e n H1)) m H2)) = pi1 … (alpha2_e e m H3). 
@Environment_simple_ind2
[//]
#e * * #y #b #HI #n #m #H1 #H2 #H3 #KK whd in match (alpha2_e ? ? ?); lapply H2
whd in match (alpha2_e (Snoc ? ?) ? ?); -H2 #H2
whd in match (alpha2_e (Snoc ? ?) ? ?); @eq_f2 // lapply H2
generalize in match (alpha_e_aux3 ? ? ? ? ?); #Hc #H2
generalize in match (alpha_e_aux3 ? ? ? ? ?); #Hb
generalize in match (alpha_e_aux2 ? ? ? ? ? ? ?); #Ha
generalize in match (alpha_e_aux2 ? ? ? ? ? ? ?); #Hd 
lapply Hd
> (alpha_e_comm (pi1  …
      (alpha2_e e (S n) Hc)) y n (S m) Ha Hb)
[ 2: @(le_S … (le_maxl … (le_maxr … H2)))
| 4: @(transitive_le … (le_S … (le_maxl … (le_maxr … H2))))
  @(le_S … (le_maxl … (le_maxr … H1)))
| 3:  cases alpha2_e #E #h @h % // @(le_maxl … H1)
| 5: lapply (alphae_domain_bound e (S n) Hc y) >alphae_eq cases domb_e // #HH @False_ind
  elim (HH (refl …)) -HH #HH#_ lapply (transitive_le … (le_S … HH) (le_maxl … (le_maxr … H1)) ) @le_Sn_n
| 7: lapply (alphae_fresh_var e (S n) Hc) #HBUONA
  <plus_n_Sm in KK; #KK lapply(le_S … (transitive_le … HBUONA KK))
  >alphae_eq // ]
[ lapply ss_over_ss * * * * #_ #_ #Hee #_ #_ #HJ >Hee
  [ @to_sse // @HI <plus_n_Sm in KK; #KK @le_S @KK ]
  [ generalize in match (?:(fresh_var_e (pi1 … (alpha2_e ? ? ?)) ≤ S m));
    lapply (alphae_fresh_var e (S n) Hc) <alphae_eq
    generalize in match (alpha2_e e ? ?); * #AA #HH  #HBUONA #l
    generalize in match (alpha2_e AA ? ?); * #BB #JJ @JJ % //
    <plus_n_Sm in KK; #KK @((transitive_le … HBUONA KK))
  | generalize in match (?:(fresh_var_e (pi1 … (alpha2_e ? ? ?)) ≤ S m)); #l @inb_alpha2_strong
    // lapply (le_maxl … (le_maxr … H2)) /2/ ] ]skip
qed.

lemma alpha_idem: ∀e, b, n, m, H1, H2, H3. m ≥n + e_len e →
 (pi1 … (alpha_c (pi1 … (alpha b e n H1)) m H2)) = pi1 … (alpha b e m H3).
#e #b #n #m #H1 #H2 #H3 lapply H2
>alpha_be_to_gamma #H2
change with (alpha ? ? ? ?) in match (alpha_c ? ? ?);
>alpha_be_to_gamma >alpha_be_to_gamma #K @eq_f2
[ 2: lapply H3 lapply H2 <alphae_eq #H2 <alphae_eq #H3 <alphae_eq /2/
| cut (∀x, H1, H2, H3. (pi1 … (alpha2_e (pi1 … (alpha2_e (push e [x←b]) n H1)) m H2)) = pi1 … (alpha2_e (push e [x←b]) m H3))
  [ #x #H11 #H22 #H33 @alpha_e_idem @H33 

lemma ssc_step_back1: ∀b, e, w, b', x, y, H1, H2, H3. 
 domb_e x e = true → veqb x w = false → 
  〈b, Snoc (sse e x y H1)[w←ssb b' x y H2]〉 = ssc 〈b, Snoc e [w←b']〉 x y H3.
  #H8 #H9 #H10 #H11 #H12 #H13 #H14 #H15 #H16 #H17 #H18
  whd in match (ssc ? ? ? ?); whd in match (domb_e ? ?); >H18 >if_f  >H17 >if_t
  whd in match (sse (Snoc ? ?) ? ? ?); >H18 >if_f // qed.
  
  
lemma sf: ∀ y, b, e, w, d, n, H3.  
  (inb y
   (pi1 … (alpha_c 〈b,Snoc e [w←d]〉 n H3))
   =false) →   
 (inb y
  (pi1 … 
   (alpha_c 〈b,e〉 (S n) (alpha_aux1 b e [w←d] n H3)))
  =false).
#y #b #e #w #d #n #H3 whd in match (alpha_c ? ? ?);
whd in match (alpha_c ? ? ?); cases (alpha ? ? ? ?) #fg #hg
whd in match (match ? in Sig with [_⇒?]);

aggiungere l'ipotesi non riduttiva che la variabile sostituenda sia maggiore uguale a n e minore di sn
whd in match (at ? ?);






lemma alpha_commutation: ∀e, b, n, x, y, H1, H2, H3, H4.

pi1 … (alpha_c … (ssc 〈b, e〉 x y H1) n H2) = ssc (pi1 … (alpha_c … 〈b, e〉 n H3)) x y H4.
@Environment_simple_ind2 [#H1 #H2 #H3 #H4 // ]
#e * #w #d #HI #b #n #x #y #H1 whd in match (ssc ? ? ? ?);
whd in match (sse ? ? ? ?);
cut (veqb x w = true ∨ veqb x w = false) // * #Hxw >Hxw
[ >if_t whd in match (domb_e ? (Snoc ? ?)); >Hxw >if_t #H2 #H3
  whd in match (alpha_c (CCrumble ? ?) ? ?);
  whd in match (alpha_c ? ? ?);
  generalize in match ((alpha_aux1 b e
    [w←ssb d x y (alpha_lemma7 y e w d (alpha_lemma1 y b (Snoc e [w←d]) H1))] n
    H2));
  cut (∀b, e, n, l, k. alpha b e n l = alpha b e n k) [//] #pi #l >pi [ 2:@l]
  generalize in match (alpha b e (S n) l); * * #bb #ee #h 
  whd in match (match ?  in Sig with [_⇒?]);
  whd in match (match ?  in Sig with [_⇒?]); #H4
  cut (∀c, x, y, j, k. ssc c x y j =ssc c x y k) [//] #pi2 lapply H4
  generalize in match (alpha_aux3 b e 〈bb,ee〉 n w d h H3); #ty
  >(pi2 (CCrumble bb ee)) [2:@ty]
  whd in match (ssc ? ? ? ?);
  cut (domb_e w ee = true ∨ domb_e w ee = false) // * #Hdee
  [ >Hdee >if_t -H4 #H4 whd in match (at ? ?);
  whd in match (at ? ?);
  whd in match (concat ? ?);
  whd in match (concat ? ?); elim (veqb_true_to_eq x w) #Heq #_ lapply (Heq Hxw)
  -Heq #Heq destruct whd in match (ssc ? ? ? ?); >domb_concat_distr >dom_sse
  >Hdee >if_t @eq_f2 // whd in match (concat ? ?); whd in match (concat ? ?);
  whd in match (sse (Snoc ? ?) ? ? ?); cut (veqb w (νn) = false)
  [ cut (veqb w (νn) = true ∨ veqb w (νn) = false) // * // #Hwn
    elim (veqb_true_to_eq w νn) #Heq #_ lapply (Heq Hwn) -Heq #Heq destruct
    @False_ind lapply (le_maxl … (le_maxr … (le_maxr … H3))) @le_Sn_n ]
  #Hwn >Hwn >if_f whd in ⊢(? ? % %); @eq_f2 //
  lapply ssc_fv * * * * #_ #_ #He #_ #_
  >(He ? w y) // lapply ssc_gnam_gnam * * * * -He #_ #_ #He #_ #_ @He @Hwn ]
  >Hdee >if_f
  whd in match (at ? ?);
  whd in match (concat ? ?); >concat_e_epsilon
  whd in match (at ? ?);
  whd in match (concat ? ?); >concat_e_epsilon -H4
  #H4  whd in match (ssc ? ? ? ?);
  whd in match (domb_e ? ?); >dom_sse 
  elim (veqb_true_to_eq x w) #Heq #_ lapply (Heq Hxw)
  -Heq #Heq destruct >Hdee >if_then_true_else_false
  cut (veqb w (νn) = false)
  [ cut (veqb w (νn) = true ∨ veqb w (νn) = false) // * // #Hwn
    elim (veqb_true_to_eq w νn) #Heq #_ lapply (Heq Hwn) -Heq #Heq destruct
    @False_ind lapply (le_maxl … (le_maxr … (le_maxr … H3))) @le_Sn_n ] #Hwn
    >Hwn >if_f @eq_f2
    [   lapply ssc_fv * * * * #_ #Hb #_  #_ #_
  >(Hb ? w y) // lapply ssc_gnam_gnam * * * * -Hb #_ #Hb #_ #_ #_ @Hb @Hwn ]
  whd in match (sse (Snoc ? ?) ? ? ?); >Hwn >if_f whd in ⊢(? ? % %); @eq_f2 //
      lapply ssc_fv * * * * #_ #_ #He #_ #_
  >(He ? w y) // lapply ssc_gnam_gnam * * * * -He #_ #_ #He #_ #_ @He @Hwn ]
>if_f whd in match (domb_e ? ?); >Hxw >if_f
cut (domb_e x e = true ∨ domb_e x e = false) // * #Hde >Hde
[ >if_t #H2 #H3 #H4 whd in match (alpha_c (CCrumble ? (Snoc ? ?)) n H3);
whd in match (alpha_c (CCrumble ? (Snoc ? ?)) n H2);
<alpha_c_to_alpha

lapply (HI b (S n) x y ? ? ? ?)
[ 2: @(alpha_aux1 b e [w←d] n H3)
| 5: whd in match (alpha_c (CCrumble b e) (S n) (alpha_aux1 b e [w←d] n H3));
   cases (alpha b e (S n) ?)
[ 4: elim (orb_false … H1) #Ha #Hb elim (orb_false … Hb) -Hb #Hb #_
      normalize >Ha >Hb //
| 5:
| 3: lapply ss_fresh_var * * * * #Hc #_ #_ #_ #_
| 5: whd in match (alpha_c ? (S n) ?);
       whd in match (ssc ? ? ? ?); lapply H4 >Hde
[ 2: @(alpha_lemma1 y b (Snoc e [w←d]) H1)
  

  cut (domb_e w ee = true) cases ssc #gh #hj 
  whd in match (at ? ?);
  whd in match (at ? ?);
  whd in match (concat ? ?);
  whd in match (concat ? ?); #H4 whd in match (ssc ? ? ? ?);









(*
lemma alpha_absorbance: ∀c, x, y, z, n, m, P1, H1, P2, H2, P3, H3.
 pi1 … (alpha2_c … (ssc (pi1 … (alpha2_c (ssc c x y P1) n H1)) y z P2) m H2) = pi1 … (alpha2_c (ssc c x z P3) m H3).
* #b
@Environment_simple_ind2
[ #x #y #z #n #m #P1 #H1 #P2 #H2 #P3 #H3
  whd in match (ssc (CCrumble b Epsilon) ? ? ?);
  whd in match (ssc (CCrumble b Epsilon) ? ? P3);
  whd in match (ssc (CCrumble (ssb ? ? ? ?) Epsilon) ? ? P2); @eq_f2 //
  lapply ss_over_ss * * * * #_ #Hb #_ #_ #_ >Hb //
| #e * #w #b' #HI #x #y #z #n #m #P1 #H1 #P2 #H2 #P3 #H3
  lapply H3 lapply H2 lapply P2 lapply H1
  whd in match (ssc ? x y P1);
  whd in match (ssc ? x z P3);
  whd in match (sse ? x y ?);
  whd in match (sse ? x z ?);
  cut (veqb x w= true ∨ veqb x w= false) [//] * #Hwx
  [ >Hwx in ⊢%; >if_t >if_t #H1
    whd in match (alpha2_c (CCrumble (ssb ? ? ? ?) ?) ? ?); lapply H1
*)
  

lemma alpha_e_absorbance: ∀e, n, m, H1, H2, H3.

pi1 … (alpha2_e (pi1 … (alpha2_e e n H1)) m H2) = pi1 … (alpha2_e e m H3).
@Environment_simple_ind2
[ #n #m #H1 #H2 #H3 //
| #e * #y #b #HI #n #m #H1 #H2 #H3 whd in match (alpha2_e ? ? ?);
  whd in match (alpha2_e (Snoc ? ?) ? ?);
  whd in match (alpha2_e (Snoc ? ?) ? ?); @eq_f2 //
  

lemma
 alpha_absorbance: ∀e, b, n, m, H1, H2, H3.
 pi1 … (alpha_c … (pi1 … (alpha b e n H1)) m H2) = pi1 … (alpha b e m H3).
@Environment_simple_ind2
[ #b #n #m #H #H' #K normalize //
| #e * * #y #b' #HI #b #n #m #H1 
  >alpha_be_to_gamma #H2 #H3 >(alpha_be_to_gamma b (Snoc e ?) ? H3)
  whd in match (alpha_c ? ? ?);
  >alpha_eq lapply H2
  <alphae_eq
  whd in match (alpha2_e ? ? ?);
  <alphae_eq
  whd in match (alpha2_e (Snoc ? ?) ? ?); #H2
  <alpha_eq >alpha_be_to_gamma
  <alphae_eq
  whd in match (alpha2_e (Snoc ? ?) ? ?);
  @eq_f2 [2: @eq_f2 [2: //]
   whd in match (alpha2 ? ? ? ?);
  whd in match (alpha_c ? ? ?);
  whd in match  (alpha2_c 〈b,Snoc e [νy←b']〉 n H1);
  lapply H1 <alpha_eq
  lapply (HI (S n) (S m) ? ? (le_S_S … ))
  [ <(plus_n_Sm) in K; @lt_to_le1
  | 3: @(alpha_aux1 b e [νy←b'] n H)
  | change with (alpha ? ? ? ?) in match (alpha_c ? ? ?);
    lapply (alpha_fresh_var e b (S n) (alpha_aux1 b e [νy←b'] n H))
    >alpha_eq
     cut (S n + e_len e ≤ S m)
     [ @le_S normalize <plus_n_Sm in K; //]
     #HH #HJ @(transitive_le … HJ HH)
   ]
   
   whd in match (alpha2_c 〈b,e〉 (S m) ?);
   whd in match (alpha2_c 〈b,e〉 (S n) ?);
   whd in match (alpha2_c 〈b, Snoc e ?〉 (n) ?);
   whd in match (alpha2_c 〈b, Snoc e ?〉 (m) ?);
   whd in match (at ? ?);
   whd in match (at ? (Snoc Epsilon ?));
   >(alpha_be_to_gamma b e (S m))
   whd in match (alpha_c 〈b,e〉 (S n) ?);
   generalize in match (alpha_aux1 b e [νy←b'] n H); #YY
   generalize in match (transitive_le ? ? ? ? ?); #LL
   >(alpha_be_to_gamma b e (S n)) in LL ⊢%; #LL
   whd in match (alpha_c ? (S m) ?);
   >alpha_be_to_gamma #HII
   cut (∀b, e, n, H, K. alpha b e n H = alpha b e n K) [//] #alpha_pi
   whd in match (alpha_c ? ? ?) in H'; lapply H'
   generalize in match (alpha_aux1 b e [νy←b'] n H); #P -H' #H'
   generalize in match ((transitive_le
     (fresh_var
      (pi1 … (alpha b e (S n) P)))
     (S n+e_len e) (S m) (alpha_fresh_var e b (S n) P)
     (le_S (S n+e_len e) m
      (eq_ind ℕ (S (n+e_len e))
       (λx_326:ℕ.λ_x_327:S (n+e_len e)=x_326.x_326≤m→S (n+e_len e)≤m)
       (λauto:S (n+e_len e)≤m.auto) (n+S (e_len e)) (plus_n_Sm n (e_len e)) K))));
   #P1
   generalize in match ((transitive_le (fresh_var 〈b,e〉) (S n+e_len_c 〈b,e〉) (S m)
     (le_plus_a_r (e_len_c 〈b,e〉) (fresh_var 〈b,e〉) (S n) P)
     (le_S_S (n+e_len_c 〈b,e〉) m
      (eq_ind ℕ (S (n+e_len e))
       (λx_326:ℕ.λ_x_327:S (n+e_len e)=x_326.x_326≤m→n+e_len_c 〈b,e〉≤m)
       (lt_to_le1 (n+e_len e) m) (n+S (e_len e)) (plus_n_Sm n (e_len e)) K))));
   #P2   
  change with (alpha ? ? ? ?) in match (alpha_c 〈b, Snoc ? ?〉  m ?);
  >(alpha_be_to_gamma b ? m)
  whd in match (alpha_c 〈b, e〉 ? ?);
  >alpha_be_to_gamma in H' P2 P1 ⊢ %; #H'
  whd in match (alpha_c ? ? H');
  >(alpha_be_to_gamma ? ? m H') #P2 #P1
  whd in match (alpha_e ? ? ?);
  [
  cases (alpha b e (S n) P) in H' P1 ⊢ %; * #bb #ee #hh
  whd in match (match «CCrumble bb ee,hh»
          in Sig
          with 
         [mk_Sig
          (a:Crumble)
           
          (h0:(∀m0:ℕ.fresh_var 〈b,e〉≤m0∧m0<S n→inb (νm0) a=false))⇒
          «at (ssc a (νy) (νn) (alpha_aux3 b e a n (νy) b' h0 H))(Snoc Epsilon [νn←b']),
          alpha_aux4 b e a n (νy) b' (alpha_aux3 b e a n (νy) b' h0 H) h0 H»]);
  #H' #P1 whd in match (ssc ? ? ? ?);
  lapply H' -H'
  whd in match (at ? ?); whd in match (concat ? ?); >concat_e_epsilon #H'
  change with (alpha ? ? ? ?) in match (alpha_c ? m H'); 
  lapply H' whd in match (alpha_c ? ? ?) in H'; #H'
  whd in match (alpha ? (Snoc ? ?) ? ?);
  whd in match (alpha_c ? ? ?);
  check alpha_be_to_gamma
  >alpha_be_to_gamma
  >alpha_be_to_gamma #HHI destruct @eq_f2
  [2: whd in match (alpha_e ? ? ?);
  whd in match (alpha ? (Snoc ? ?) ? ?);
  whd in match (beta_e ? ?); 
  whd in match (alpha_e ? ? ?);
  whd in match (gamma_b ? ? ?); @eq_f2
  
  [ generalize in match (gamma_b_aux2 ? ? ? ?); #GBA2
    generalize in match (gamma_b_aux3 ? ? ? ? ? ?); #GBA3
    generalize in match (alpha_lemma2 ? ? ? ?); #AL2
    generalize in match (alpha_lemma2 ? ? ? ?); #AL22
