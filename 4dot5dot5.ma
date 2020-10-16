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

include "alpha.ma".

let rec cc_aux_read_back rbt ec on ec ≝ 
 match ec with
 [ envc e x ⇒ hole_subst (aux_read_back rbt e) x
 ]
 .

definition cc_read_back  ≝ λ(cc:CrumbleContext).
 match cc  with
 [ hole ⇒ (thole: TermContext)
 | crc b ec ⇒ (cc_aux_read_back (read_back_b b) ec)
 ]
 .

let rec fresh_vua_t t on t ≝
 match t with
 [ val_to_term v ⇒ fresh_vua_tv v
 | appl t1 t2 ⇒ max (fresh_vua_t t1) (fresh_vua_t t2)
 ]
 
and fresh_vua_tv v on v ≝
 match v with
 [ pvar x ⇒ 0
 | abstr z t ⇒ fresh_var_t t
 ] 
.

let rec fresh_vua c on c ≝
 match c with
 [ CCrumble b e ⇒ max (fresh_vua_b b) (fresh_vua_e e) ]
 
and fresh_vua_b b on b ≝ 
 match b with
 [ CValue v ⇒ fresh_vua_v v
 | AppValue v w ⇒ max (fresh_vua_v v) (fresh_vua_v w)
 ]
 
and fresh_vua_v v on v ≝
 match v with
 [ var x ⇒ 0
 | lambda x c ⇒ fresh_var c
 ]

and fresh_vua_e e on e ≝
 match e with
 [ Epsilon ⇒ 0
 | Cons e s ⇒ max (fresh_vua_e e) (fresh_vua_s s)
 ]

and fresh_vua_s s on s ≝
 match s with
 [ subst y b ⇒ fresh_vua_b b ]
.

lemma fresh_vua_push:
 ∀e, s. fresh_vua_e (push e s) = fresh_vua_e (Cons e s).
@Environment_simple_ind2 //
#e #s #HI #s1 whd in match (push ? ?); whd in match (fresh_vua_e ?); >HI
change with (max ? ?) in match (if ? then ? else ?);
change with (max ? ?) in match (fresh_vua_e ?);
change with (max ? ?) in match (fresh_vua_e (Cons (Cons e s) s1));
change with (max ? ?) in match (fresh_vua_e (Cons e s));
// qed.

lemma fresh_vua_concat:
 ∀f, e. fresh_vua_e (concat e f)= max (fresh_vua_e e) (fresh_vua_e f).
@Environment_simple_ind2
[ #e >concat_e_epsilon whd in match (fresh_vua_e Epsilon); >max_O @refl ]
#f #s #HI #s1 whd in match (concat ? ?);
whd in match (fresh_vua_e (Cons ? ?)); >HI
change with (max ? ?) in match (fresh_vua_e (Cons ? ?));
change with (max ? ? = max ? ?) //
qed.
 
lemma tc_lemma: (∀t.∀x. fvb_t x t = false → match t with
  [ val_to_term v ⇒ tc_value (hole_subst (val_to_term v) x)
  | appl t1 t2 ⇒ tc_term (hole_subst (appl t1 t2) x)
  ]) ∧
(∀v.∀x. fvb_tv x v= false → tc_value (hole_subst (val_to_term v) x)).
@pifValueTerm_ind
[ #v normalize #H @H
| 3: #z #x normalize >veqb_comm cases veqb normalize // #abs destruct
| 4: #t #z #HI #x normalize >veqb_comm cases veqb normalize // #H
  lapply no_hole_lemma * #Ht #_ @Ht @H
| #t1 #t2 #H1 #H2 #x #H
  cut (free_occ_t x t1=0 ∧ free_occ_t x t2=0)
  [ lapply H normalize cases free_occ_t
    normalize
    [ cases free_occ_t normalize [ #_ % // ]
      #n #abs destruct
    | #n #abs destruct
    ] ]
  * #Ha #Hb normalize lapply no_hole_lemma * #Ht #_ % @Ht normalize
  [ >Ha // | >Hb // ]
] qed.

let rec nhua T on T ≝
 match T with 
 [ thole ⇒ True
 | term t ⇒ True
 | c_appl u1 u2 ⇒ nhua u1 ∧ nhua u2
 | c_abstr x T ⇒ tc_term T
 ]
 .
 
lemma term_nhua: ∀T. tc_term T → nhua T .
@TermContext_ind
[ normalize //
| #t normalize //
| #t1 #t2 #H1 #H2 normalize* #Ha #Hb % [ @H1 // | @H2 // ]
| #x #T #H normalize //
] qed.

lemma tc_value_term: ∀T. tc_value T → tc_term T.
*
[ normalize //
| * #t normalize //
| #t1 #t2 normalize #H @False_ind @H
| #x #T normalize #abs @abs
] qed.

lemma tc_term_conservative: ∀T, U. tc_term T → tc_term (plug_T T U).
@TermContext_ind
[ #U normalize #abs @False_ind @abs
| #t #U normalize //
| #u1 #u2 #H1 #H2 #U normalize * #Ha #Hb % [ @H1 // | @H2 @Hb ]
| #x #U #HI #U normalize @HI
] qed.

lemma tc_value_conservative: ∀T, U. tc_value T → tc_value (plug_T T U).
@TermContext_ind
[ #U normalize #abs @False_ind @abs
| #t #U normalize #H @H
| #u1 #u2 #H1 #H2 #U normalize //
| #x #U #HI #U normalize @tc_term_conservative
] qed.

lemma rv_nhua: ∀T. rv_context T → nhua T.
@TermContext_ind
[ normalize //
| #t normalize //
| #t1 #t2 normalize #H1 #H2 *
  [ * #Ha #Hb % [ @term_nhua @Ha ] @(H2 Hb)
  | * #Ha #Hb % [ @H1 @Ha ] @term_nhua @tc_value_term @Hb
  ]
| #x #T normalize #_ #abs @False_ind @abs
] qed.

lemma tcterm_fvb:
 (∀t, x. tc_term (hole_subst t x) → fvb_t x t = false) ∧
  (∀v, x. tc_term (hole_subst (val_to_term v) x) → fvb_tv x v = false).
@pifValueTerm_ind
[ #v #H @H
| #t1 #t2 #H1 #H2 #x normalize * #Ha #Hb lapply (H1 … Ha) lapply (H2 … Hb)
  normalize cases free_occ_t cases free_occ_t normalize //
| #z #x normalize >veqb_comm cases veqb normalize // #abs @False_ind @abs
| #t #z #HI #x normalize >veqb_comm cases veqb normalize // @HI
] qed.

lemma hole_subst_nhua:
 (∀t, x. nhua (hole_subst t x) → nua_t x t = true) ∧
  (∀v, x. nhua (hole_subst (val_to_term v) x) → nua_tv x v = true).
@pifValueTerm_ind
[ #v #H @H
| #t1 #t2 #H1 #H2 #x
  whd in match (hole_subst ? ?);
  whd in match (nhua ?); * #Ha #Hb
  whd in match (nua_t ? ?); >H1 // >H2 //
| #z #x normalize //
| #t #z #HI #x normalize cases veqb normalize // 
  change with (fvb_t x t) in match (gtb ? ?); #H
  lapply tcterm_fvb * #Ht #_ >Ht // 
] qed.

lemma rv_composition: ∀T,U.
 rv_context T →
  rv_context U → 
   rv_context (plug_T T U).
@TermContext_ind
[ #U normalize #_ #H @H
| #t #U normalize #H #_ @H
| #u1 #u2 #H1 #H2 #U normalize *
  [ * #Ha1 #Ha2 #Hb @or_introl %
    [ @tc_term_conservative @Ha1
    | @(H2 U Ha2 Hb)
    ]
  | * #Ha1 #Ha2 #Hb @or_intror %
    [ @(H1 U Ha1 Hb)
    | @tc_value_conservative @ Ha2
    ]
  ]
| #x #T #H #U normalize #abs #_ @abs
] qed.

lemma pre_disaster_lemma: ∀f,g,s,t.
(push Epsilon s=concat (Cons f t) g) →
 s=t ∧ f=Epsilon ∧g=Epsilon.
#f #g #s #t normalize
cases f
[ cases g normalize
  [ #H destruct % // % //
  | #e #s #H destruct lapply e0
    cases e [ normalize -H #H destruct ]
    #j #k normalize #abs destruct
  ]
| #e #s cases g
  [ normalize #H destruct
  | #j #k normalize #H destruct
    lapply e0 cases j normalize [ #abs destruct ]
    #u #y normalize #abs destruct
  ]
] qed.

lemma nearly_disaster_lemma_aux: 
 ∀e,gg,s,t. (push e s=concat (Cons Epsilon t) gg) → 
  s=t ∧ e = gg.
@Environment_double_ind2

[ #s #t normalize #H destruct % //
| *
  [ #s #t #u normalize #H destruct
  | #ee #ss #s #t #u normalize #H destruct
  ]
| #e #s #t #u normalize #H destruct
  lapply e0 cases e
  [ normalize #e1 destruct
  | #ee #ss normalize #H1 destruct
  ]
| #e #f #s #t #HI #ss #tt
  whd in match (push ? ?);
  whd in match (concat ? ?); #H
  cut (push e ss = concat (Cons Epsilon tt) f)
  [ destruct @e0] #e0
  lapply (HI … e0) * #Ha #Hb % // >Hb @eq_f2 //
  lapply H cases push
  [ cases concat
    [ -H #H destruct //
    | #gg #hh -H #H destruct
    ]
  | #rr #yy cases concat
    [ -H #H destruct
    | #gg #hh -H #H destruct //
    ]
  ]
] qed.

lemma nearly_disaster_lemma: ∀e,g,s,t.
(push e s=concat (Cons Epsilon t) g) →
s=t ∧ e = g.
*
[ #g #s #t normalize
  cases g
  [ normalize #H destruct % [ % @refl ] @refl ]
  #gg #ssg normalize #H destruct
  lapply e0 cases gg
  [ normalize #hh destruct
  | #ll #kk normalize #hh destruct
  ]
| #e #s #g #s #t whd in match (push ? ?); cases g
  [ normalize #H destruct lapply e0 cases e
    [ normalize #h destruct
    | #e #s normalize #h destruct
    ]
  | #gg #ggs normalize #H
    cut ((push e s=concat (Cons Epsilon t) gg))
    [ destruct @e0 ] #e0
    lapply (nearly_disaster_lemma_aux … e0) * #Ha #Hb
    destruct (Ha Hb) % // @eq_f2 //
    lapply H cases push
    [ cases concat
      [ #HH destruct //
      | #f #g #H destruct
      ]
    | #ee #ss cases concat
      [ #HH destruct
      | #f #g #HH destruct //
      ]
    ]
  ]
] qed.

lemma disaster_lemma: ∀e,g,f,s,t,u,v.
(push (Cons e s) t=concat (Cons (Cons f v) u) g) →
∃d. ((Cons f v) = push d t) ∧ (Cons e s) = concat (Cons d u) g.
@Environment_double_ind2
[ #f #s #t #u #v normalize #H destruct % [@Epsilon] % //
| #e #se #f #s #t #u #v normalize cases e
  [ normalize #H destruct % [ @(Cons Epsilon v) ] normalize % //
  | #e1 #se1 normalize #H destruct % [ @(Cons (Cons e1 se1) v) ] normalize % //
  ]
| #g #sg #f #s #t #u #v normalize #H
  cut (e_len (Cons (Cons Epsilon t) s) ≠ e_len (Cons (concat (Cons (Cons f v) u) g) sg))
  [ normalize >concat_len normalize % #abs destruct ]
  #Hf @False_ind elim Hf -Hf #Hf @Hf >H @refl
| #e #g #ss #tt #HI #f #s #t #u #v
  whd in match (push ? ?);
  whd in match (concat ? ?);
  #H
  cut (push (Cons e ss) t=concat (Cons (Cons f v) u) g)
  [ destruct @e0] #e0
  lapply (HI … e0) -e0 -HI #HI
  elim HI #x * #Ha #Hb % [ @x ] normalize %
  [ @Ha ] >Hb @eq_f2 //
  lapply H -H cases push
  [ cases concat [ #H destruct // ] #e #s #H destruct 
  | #e #s cases concat [ #H destruct ] #m #i #H destruct //
  ]
] qed.

lemma push_eq_concat_cons: ∀e, s, f, t, g.
 push e s = concat (Cons f t ) g →
   (s=t ∧ e = g ∧ f= Epsilon) ∨
    (∃d. f = push d s ∧ e = concat (Cons d t) g).
#e #s #f #t #g cases e
[ #H lapply (pre_disaster_lemma … H) * * * * * @or_introl % % %
| #e #u cases f
  [ >concat_to_push  #H lapply(push_eq_inv … H) * * * @or_introl % % %
  | #ff #ss #H lapply (disaster_lemma … H) * #X * #Ha #Hb @or_intror % [ @X ] % //
  ]
] qed.

lemma concat_switch: ∀c, a, b. concat (concat a b) c = concat a (concat b c).
@Environment_simple_ind2
[ #a #b normalize //
| #e #s #HI #a #b normalize >HI //
] qed.

lemma fvb_tcterm:
 (∀t, x. fvb_t x t = false → tc_term (hole_subst t x)) ∧
  (∀v, x. fvb_tv x v = false → tc_term (hole_subst (val_to_term v) x)).
@pifValueTerm_ind
[ #v #H @H
| #t1 #t2 #H1 #H2 #x normalize #H
  cut (fvb_t x t1 = false ∧ fvb_t x t2 = false)
  [ lapply H normalize cases free_occ_t cases free_occ_t normalize
  [ #H1 % //
  | 2,3: #n #H1 % //
  | #n #m #H1 % >H1 //
  ] ] *
   #Ha #Hb %
  [ @H1 @Ha | @H2 @Hb ]
| #z #x normalize >veqb_comm cases veqb normalize // #abs destruct
| #t #z #HI #x normalize >veqb_comm cases veqb normalize // @HI
] qed.

lemma tc_value_rb:
∀v, x. tc_term (hole_subst (read_back_v v) x) →
 tc_value (hole_subst (read_back_v v) x).
 
*
[ #x #z normalize cases veqb normalize //
| #z * #b #e #x normalize cases veqb normalize //
] qed.
lemma delirium_lemma:
 ∀e, f, g, h, s, t, u. (concat (push e s) (push f t)=concat (Cons g u) h) →
  (g=Epsilon ∧ s=u ∧ h = concat e (push f t)) ∨
   (∃d, p. g = push d s ∧ e = concat (Cons d u) p ∧ h = (concat (Cons p t) f)) ∨
    (g = push e s ∧ t = u ∧ h = f) ∨
     (g = Cons (push e s) t ∧ f = push h u) ∨
      (∃d. g = concat (Cons (push e s) t) d ∧ f = concat d (push h u)).
#e #f #g #h #s #t #u #H
lapply (concat_decomposition1 … H) * * #x * #Ha #Hb
[ destruct lapply H lapply Ha -H -Ha cases e
  [ #Ha lapply (pre_disaster_lemma … Ha) * * #H1 #H2 #H3 destruct
    >concat_epsilon_e #_ % % % % % % //
  | #ee #ss cases g
    [ #Ha lapply (nearly_disaster_lemma … Ha) *  #H1 #H2 >H1 >H2 #HH
      % % % % % % //
    | #gg #sg #Ha lapply (disaster_lemma … Ha) * #y * #H1 #H2 >H1 >H2
      normalize #H % % % @or_intror % [ @y ] % [ @x ] % [ % // ] >env_lemma2 @refl
    ]
  ]
| lapply (cons_concat … Ha) *
  [ * #Ha1 #Hx cut (Cons g u = push e s) // -Ha1 #Ha1
    lapply (cons_push_decomposition … Ha1 ) *
    [ * * #Hus #He #Hg lapply H >Hus >He >Hg normalize
      >concat_to_push >concat_to_push #HH >concat_epsilon_e %%%%%[%//]
      destruct lapply (push_eq_inv … HH) * #Heq #_ >Heq @refl
    | * #y * #Hc #Hd % % % @or_intror % [ @y ] % [ @Epsilon ] normalize
      >concat_to_push % [ % // ] lapply Hb >Hx >concat_epsilon_e //
    ]
  | * #y * #Hc #Hd destruct lapply Hb -Hb cases f
    [ #Hb lapply (pre_disaster_lemma … Hb) * * #Htu #Hy #Hh destruct % %
      @or_intror normalize % [ % @refl ] @refl
    | #ff #fs cases y
      [ #Hb lapply (nearly_disaster_lemma … Hb) * #Htu #Hh destruct % %
        @or_intror normalize % // % //
      | #yy #sy #Hb lapply (disaster_lemma … Hb) * #z * #Hc #Hd
        lapply (cons_push_decomposition … Hc) *
        [ * * #Hsyt #Hz #Hyy destruct % @or_intror normalize
          lapply Hd >concat_to_push -Hd #Hd >Hd % //
        | * #w * #He #Hf @or_intror destruct % [ @(Cons w sy) ] normalize %
          [ @eq_f2 // | >Hd // ]
        ]
      ]
    ]
  ]
] qed.

lemma alpha_e_concat_aux1: ∀f, e, n. ∀(H : (fresh_var_e (concat e f)≤n)).  
 ((∀x:Variable.rhs (beta_e (concat e f) n) x→inb_e x e=false)
  ∧distinct_rhs (beta_e (concat e f) n)).
#f #e #n #H % // * #k  #Hk elim (betae_rhs_bound … Hk) #Hnk #_ lapply H
>fresh_var_concat -H #H lapply (transitive_le … (le_maxl … H) Hnk)
lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_ @He qed.

lemma alphae_concat_aux2: ∀f, e, n.
 ∀(H : (fresh_var_e (concat e f)≤n)).  
 (fresh_var_e e≤n+e_len f).
#f #e #n >fresh_var_concat #H cut (n ≤ n+ e_len f) [//] #Hn
@(transitive_le … (le_maxl … H) Hn) qed.

lemma alpha_e_concat_aux3: ∀f, e, n.
 ∀(H : (fresh_var_e (concat e f)≤n)).
 ((∀x:Variable
   .rhs (beta_e f n) x
    →inb_e x
     (pi1 Environment
      (λd:Environment.∀m:ℕ.fresh_var_e e≤m∧m<n+e_len f→inb_e (νm) d=false)
      (alpha_e e (n+e_len f) (alphae_concat_aux2 f e n H)))
     =false)
  ∧distinct_rhs (beta_e f n)).
#f #e #n #H % // * #k #Hk elim (betae_rhs_bound … Hk) #Ha #Hb cases alpha_e
#a #h @h % // >fresh_var_concat in H; #H @(transitive_le … (le_maxl … H) (Ha)) qed.

lemma alpha_e_concat_aux2: ∀f, e, n.
 fresh_var_e (concat e f) ≤ n → fresh_var_e f ≤ (n).
#f #e #n >fresh_var_concat #H @(le_maxr … H) qed.
(*
lemma alpha_e_step: ∀e, y, b, n, H.
 pi1 … (alpha_e (Cons e [y←b]) n H) = Cons (pi1 … (alpha_e e (S n) (alpha_e_aux3 … H))) [νn←b].
@Environment_simple_ind2
[ #y #b #n #H whd in match (alpha_e ? ? ?); whd in match (sse ? ? ? ?); //
| #e #s #HI #y #b #n whd in match (alpha_e ? ? ?);
*)

lemma alpha_e_concat: ∀f, e, n, H. 
 pi1 … (alpha_e (concat e f) n H) = 
 concat (pi1 … (gamma_e (pi1 … (alpha_e e (n+(e_len f)) (alphae_concat_aux2 f e n H))) (beta_e f n) (alpha_e_concat_aux3 … H)))
        (pi1 … (alpha_e f n (alpha_e_concat_aux2 … H))).

@Environment_simple_ind2
[ #e #n whd in match (concat ? ?);
  whd in match (beta_e Epsilon ?); whd in match (e_len Epsilon ); #H
  whd in match (gamma_e ? [] ?); whd in match (alpha_e Epsilon ? ?);
  >concat_e_epsilon
  generalize in match (alphae_concat_aux2 ? ? ? ?);
  generalize in match H; cut (n+0 = n) [//] #Hn >Hn //
| #f * #y #b #HI #e #n
  whd in match (beta_e ? ?);
  whd in match (e_len ?); #H 
  whd in match (alpha_e (Cons ? ?) ? ?);
  whd in match (alpha_e (Cons ? ?) ? ?);
  whd in match (gamma_e ? ? ?);
  lapply (HI e (S n) (alpha_e_aux3 n (concat e f) y b H))
  cases alpha_e #a #h whd in match (match ? in Sig with [_⇒?]);
  #Heq generalize in match (alpha_e_aux2 … h); >Heq -HI
  generalize in match (alpha_e_aux3 … (alpha_e_concat_aux2 … H)); #l
  generalize in match (alpha_e_concat_aux2 ? ? ? ?);
  cases (alpha_e f (S n) ?) #aa #hh
  whd in match ((pi1 Environment
  (λd:Environment.∀m:ℕ.fresh_var_e (Cons f [y←b])≤m∧m<n→inb_e (νm) d=false) ?));
  whd in match (concat ? (Cons ? ?)); #H1 #H2 @eq_f2 //
  >sse_concat @eq_f2
  [ 2: generalize in match (sse_concat_aux2 ? ? ? ?); // ]
  generalize in match (sse_concat_aux1 … H2);
  generalize in match (alpha_e_concat_aux3 ? ? ? ?);
  generalize in match (alphae_concat_aux2 ? ? ? ?); 
  generalize in match (gamma_e_aux2 ? ? ? ?);
  generalize in match (gamma_e_aux3 ? ? ? ? ? ?);
  generalize in match (alpha_e_concat_aux3 ? ? ? ?);
  generalize in match (alphae_concat_aux2 ? ? ? ?); <plus_n_Sm
  whd in match (S n + ?);
  #P1 #P2 #P3 #P4 #P5 #P6 #P7 //
] qed.

lemma four_dot_five_dot_five: 
 (∀t, s, c, C.
  fresh_var_t t ≤ s →  
   fst … (underline_pifTerm t s) = plug_c C c →
    rv_context (cc_read_back C)) ∧
 (∀v:pifValue. True).
@pifValueTerm_ind
[ #v #_ #s * #b #e *
  [ normalize cases overline //
  | #b' * #f #y normalize cases overline #vv #n normalize #_ #abs destruct
    @False_ind lapply e0 cases e normalize -abs #abs 
    [ destruct
    | #aa #ee destruct
    ]
  ]
| 3: //
| 4: //
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply four_dot_one_dot_one * #H411t #H411v #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s #c #C
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s c C (le_maxl … H))
      lapply (Hmono2 v1 s)
      lapply (H411v v1 s)
      cases (overline v1 s) #vv #n #Hfvv1 #Hsn normalize
      lapply (H2 s c C (le_maxr … H))
      lapply (Hmono2 v2 n)
      lapply (H411v v2 n)
      cases (overline v2 n) #ww #m #Hfvv2 normalize #Hnm
      #H2' #H1' cases C cases c #b #e normalize
      [ // ] #bb * #ee #y normalize cases e normalize #HH destruct
       #ss normalize #HH destruct
    | #u1 #u2 normalize #H1 #H2 #s * #B #E * [ normalize // ] #bb * #ee #y
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s)
      lapply (Hbound (appl u1 u2) s)
      lapply (Hldom (appl u1 u2) s)
      lapply (Hmono1 (appl u1 u2) s)
      lapply (Hline1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hline1 #Hsn #Hldom1 #Hbound1 #H1'
      lapply (H2 n)
      lapply (Hbound (val_to_term v2) n)
      lapply (Hldom (val_to_term v2) n) normalize
      lapply (Hmono2 v2 n)
      lapply (Hline2 v2 n)
      lapply (H411v v2 n)
      cases (overline v2 n) #vv #m #Hfvv2 normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hline2 #Hnm #Hldom2 #Hbound2 #H2' #Heq
      destruct
      
      lapply Hline1 lapply Hldom1 lapply Hbound1 lapply H1' lapply H2' lapply e0
      -Hline1 -Hldom1 -Hbound1 -H1' -H2' -e0
      cases e
      [ #e0 lapply (pre_disaster_lemma … e0)  * * #ha #hb #hc destruct
        normalize #_ #_ #_ #_ change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
        change with (max ? ?) in match (if leb ? ? then 0 else ?);
        >max_O #HA >neqb_refl >if_t normalize @or_intror % // @tc_value_rb
        lapply fvb_tcterm * #Ht #_ @Ht cut (inb_v (νm) vv = false)
        [ lapply (Hline2 (transitive_le … (le_maxr … H) Hsn))
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_
          @Hv ]
        #Hin lapply fv_lemma * * * * #_ #_ #_ #Hv #_
        cut (fvb_v (νm) vv = false)
        [ lapply Hin @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 @Hv ]
      ] #et #ciu cases ee
      [ #e0 lapply (nearly_disaster_lemma … e0) * #Ha #Hb destruct
        #_ #H1 #Hdom1 #hdom2 #Hlineline normalize >neqb_refl >if_t normalize 
        @or_intror % // @tc_value_rb
        lapply fvb_tcterm * #Ht #_ @Ht cut (inb_v (νm) vv = false)
        [ lapply (Hline2 (transitive_le … (le_maxr … H) Hsn))
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_
          @Hv ]
        #Hin lapply fv_lemma * * * * #_ #_ #_ #Hv #_
        cut (fvb_v (νm) vv = false)
        [ lapply Hin @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 @Hv ]
      #ping #pong #e0 lapply (disaster_lemma … e0) * #x * #ha #hb destruct
      >ha >hb #HH destruct #H11 #Hdom1 #Hdom2 #Hlineline
      lapply (H11 〈B, E〉 (crc b (envc x y))) whd in match (plug_c ? ?);
      whd in match (plug_e ? ?); -H11 #H11 lapply (H11 (le_maxl … H) (refl …))
      whd in match (match ? in CrumbleContext with [_⇒?]); -H11 #H11
      normalize >aux_read_back1
      whd in match (hole_subst ? ?);
      whd in match (rv_context ?);
      @or_intror >push_lemma
      whd in match (match ?  in Substitution with [_⇒?]);
      >atomic_subst % [ @H11 ] >push_lemma
      whd in match (match ?  in Substitution with [_⇒?]);
      >no_subst5
      [ 2: cut (inb_v (νm) vv = false)
      [ lapply (Hline2 (transitive_le … (le_maxr … H) Hsn))
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_
          @Hv ]
        #Hin lapply fv_lemma * * * * #_ #_ #_ #Hv #_
        cut (fvb_v (νm) vv = false)
        [ lapply Hin @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 @Hv ]
      >stronger_aux_read_back3
      [ 2: * #z #Htmp cut (fvb_v (νz) vv = false)
        [ cut (s ≤ z)
          [ @Hdom2 >domb_concat_distr normalize
            >Htmp >if_monotone >if_t @refl ]
          #Hsz <(Hfvv2 … (transitive_le … (le_maxr … H) Hsn))
          lapply (transitive_le …  (le_maxr … H) Hsz) -Htmp #Hfv
          cut (inb_tv (νz) v2 = false)
          [ lapply Hfv lapply (fresh_var_to_in) * #_ #Hv @Hv ]
          @bool_impl_inv2 lapply fv_to_in_term * #_ #Hv @Hv ]
        @bool_impl_inv2 lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @Hv ]
        @tc_value_rb lapply fvb_tcterm * #Ht #_ @Ht
        lapply Hdom2 cases y #ny -Hdom2 #Hdom2
        cut (fvb_v (νny) vv = false)
        [ cut (s ≤ ny)
          [ @Hdom2 >domb_concat_distr normalize >neqb_refl >if_t @refl ]
          #Hsz <(Hfvv2 … (transitive_le … (le_maxr … H) Hsn))
          lapply (transitive_le …  (le_maxr … H) Hsz) #Hfv
          cut (inb_tv (νny) v2 = false)
          [ lapply Hfv lapply (fresh_var_to_in) * #_ #Hv @Hv ]
          @bool_impl_inv2 lapply fv_to_in_term * #_ #Hv @Hv ]
        @bool_impl_inv2 lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @Hv
 | #u1 #u2 normalize #H1 #H2 #s
   lapply (H2 s)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hbound (appl u1 u2) s)
    lapply (Hldom (appl u1 u2) s)
    lapply (Hmono1 (appl u1 u2) s)
    lapply (Hline1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hbound (val_to_term v1) n)
      lapply (Hldom (val_to_term v1) n) normalize
      lapply (Hmono2 v1 n)
      lapply (Hline2 v1 n)
      lapply (H411v v1 n)
      cases (overline v1 n) #vv #m
      normalize
      change with (fresh_var_tv ?)
        in match (pi1 ? ? (fresh_var_tv_Sig ?));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (max ? ?)
        in match (if ? then fresh_var_t ? else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e ? else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?); #Hfvv1
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2 * #B #E * [ normalize // ] #bb * #ee #y
      #Hm >concat_epsilon_e
      whd in match (plug_c ? ?);
      whd in match (plug_e ? ?);
      whd in match (match ? in CrumbleContext with [_⇒?]);
      #Heq destruct normalize >aux_read_back1 whd in match (hole_subst ? ?);
      -Heq
      
      lapply e0 -e0 lapply H2 -H2 lapply Hbound2 -Hbound2 lapply Hldom2 -Hldom2
      lapply Hline2 -Hline2 -Hldom1 -Hbound1 -H1
      cases e1
      [ whd in match (fresh_var_e ?); >max_O #Hline2 #_ #_ #H2'
        whd in match (push ? ?); #e0
        lapply (pre_disaster_lemma … e0)  * * #ha #hb #hc destruct normalize
        >neqb_refl >if_t normalize @or_introl % // lapply fvb_tcterm * #Ht #_
        @Ht cut (inb_v (νm) vv = false)
        [ lapply (Hline1 (transitive_le … (le_maxl … Hm) Hsn))
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_
          @Hv ]
        #Hin lapply fv_lemma * * * * #_ #_ #_ #Hv #_
        cut (fvb_v (νm) vv = false)
        [ lapply Hin @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 @Hv ]
      #ee1 #se1 change with (max ? ?) in match (fresh_var_e ?); #Hline2
      #Hdom1 #Hdom2 #H2' cases ee
      [ #Heq lapply (nearly_disaster_lemma … Heq) * #Ha #Hb destruct
        normalize >neqb_refl normalize @or_introl % //
        cut (inb_v (νm) vv = false)
        [ lapply (Hline1 (transitive_le … (le_maxl … Hm) Hsn))
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_
          @Hv ]
        #Hin lapply fv_lemma * * * * #_ #_ #_ #Hv #_ lapply fvb_tcterm * #Ht #_
        @Ht cut (fvb_v (νm) vv = false)
        [ lapply Hin @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 @Hv ]
      #ee2 #se2 #Heq lapply (disaster_lemma … Heq) * #x * #Ha #Hb
      lapply H2' -H2' lapply Hdom2 -Hdom2 lapply Hdom1 -Hdom1 lapply Heq -Heq
      >Ha >Hb destruct #Heq #Hdom1 #Hdom2 #H2' normalize
      lapply (H2' 〈B, E〉 (crc b1 (envc x y))) whd in match (plug_c ? ?);
      whd in match (match ?  in CrumbleContext with [_⇒?]);
      whd in match (plug_e ? ?);
      >(push_lemma (val_to_term (pvar νm))) whd in match (match ?  in Substitution with [_⇒?]);
      >atomic_subst -H2' #H2' @or_introl %
      [ 2: @H2' [ @(le_maxr … Hm) | @refl ] ]
      >stronger_aux_read_back3
      [ 2: * #z >dom_push whd in match (domb_e ? ?); #H
        cut (s ≤z)
        [ lapply H elim (veqb_true_to_eq (νz) νm) #HH #_ lapply HH
          cut (veqb (νz) (νm)=true ∨ veqb (νz) (νm)=false) // * #Hzm
          [ lapply (HH Hzm) -HH #HH destruct >Hzm normalize #_ #_
            @(transitive_le … Hsn Hnm)
          | #_ -HH >Hzm normalize #HH @Hdom1 >domb_concat_distr normalize >HH
            >if_monotone >if_t @refl
          ] ]
        #Hsz cut (fvb_v (νz) vv = false)
        [ <(Hfvv1 (νz) (transitive_le … (le_maxl … Hm) Hsn))
          change with (fvb_tv (νz) v1= false)
          lapply (transitive_le … (le_maxl … Hm) Hsz) #Hv1
          cut (inb_tv (νz) v1 = false)
          [ lapply Hv1 lapply (fresh_var_to_in) * #_ #Hv @Hv ]
          @bool_impl_inv2 lapply (fv_to_in_term) * #_ #Hv @Hv ]
        lapply (fv_lemma) * * * * #_ #_ #_ #Hv #_ @bool_impl_inv2 @Hv ]
      lapply fvb_tcterm * #Ht #_ @Ht
      cut (fvb_v y vv = false)
      [ lapply Hdom1 cases y #ny -Hdom1 #Hdom1
        cut (s ≤ ny)
        [ @Hdom1 >domb_concat_distr normalize >neqb_refl >if_t @refl ]
        #Hsy <(Hfvv1 … (transitive_le … (le_maxl … Hm)Hsn))
        change with (fvb_tv (νny) v1 = false)
        cut (inb_tv (νny) v1 = false)
        [ lapply (transitive_le … (le_maxl … Hm) Hsy)
          lapply (fresh_var_to_in) * #_ #Hv @Hv ]
        @bool_impl_inv2 lapply (fv_to_in_term) * #_ #Hv @Hv ]
      lapply (fv_lemma) * * * * #_ #_ #_ #Hv #_ @bool_impl_inv2 @Hv
    | #r1 #r2 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hbound (appl r1 r2) n)
      lapply (Hldom (appl r1 r2) n)
      lapply (Hmono1 (appl r1 r2) n)
      lapply (Hline1 (appl r1 r2) n)
      lapply (H411t (appl r1 r2) n)
      change with (underline_pifTerm (appl r1 r2) n)
        in match ( match r2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl r1 r2) n ) * #b #e #m #H411
      normalize
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r2));
      change with (max ? ?)
        in match (if ? then fresh_var_t r2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_t u2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e1 else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?);
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1'
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2' * #B #E * [ // ] #bb * #ee #y #Hm
      whd in match (plug_c ? ?);
      whd in match (plug_e ? ?);
      whd in match (match ?  in CrumbleContext with [_⇒?]);
      #H destruct
      
      lapply (delirium_lemma … e0) *
      [ 2: * #z * #Ha #Hb destruct >env_lemma5 >aux_read_back1
        whd in match (hole_subst ? ?);
        whd in match (read_back_v ?);
        lapply (H2' … (CCrumble B E) (crc b1 (envc z y)) ((le_maxr … Hm)))
        whd in match (plug_c ? ?);
        whd in match (plug_e ? ?);
        whd in match (match ? in CrumbleContext with [_⇒?]);
        #H2' cut (rv_context (hole_subst (aux_read_back (read_back_b b1) z) y))
        [ @(H2') <env_lemma5 @refl ] -H2' #H2'
          >(ultra_concat_lemma)
          [ 3: >dom_push change with ((if neqb ? ? then ? else ?)= false)
            >neq_simm >neqb_false >if_f lapply (Hbound2 … (S m))
            >domb_concat_distr cases domb_e // normalize #HH @False_ind
            lapply (le_S … (transitive_le … (HH (refl …)) Hnm)) @le_Sn_n
          | 2: #k >dom_push >fv_push normalize
            cut (veqb k (νm) = true ∨ veqb k (νm) = false) // * #Hkm
            [ elim (veqb_true_to_eq k νm) #Heq #_ lapply (Heq Hkm) -Heq #Heq
              destruct #_ cut (fvb_e (νm) e = false)
              [ cut (inb_e (νm) e = false)
                [ lapply (le_maxr … (Hline1 (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_ @He ]
                @bool_impl_inv2 lapply fv_to_in_crumble * * * *
                #_ #_ #He #_ #_ @He ]
              cut (fvb_b (νm) b = false)
              [ cut (inb_b (νm) b = false)
                [ lapply (le_maxl … (Hline1 (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb ]
                @bool_impl_inv2 lapply fv_to_in_crumble * * * *
                #_ #Hb #_ #_ #_ @Hb ]
              #Ha #Hb normalize >Ha >Hb normalize >if_monotone @refl ]
            >Hkm normalize cases k #nk #Hkz
            cut (s≤nk)
            [ @(Hldom2) >domb_concat_distr >Hkz normalize @refl ] #Hsnk
            cut (fvb (νnk) 〈b, e〉=false)
            [ <(H411 … (transitive_le … (le_maxl … Hm) Hsn))
              cut (inb_t (νnk) (appl r1 r2)= false)
              [ cut (fresh_var_t (appl r1 r2) ≤ nk)
                [ change with (max ? ?≤nk)
                  @(transitive_le … (le_maxl … Hm) Hsnk) ]
                lapply (fresh_var_to_in) * #Ht #_ @Ht ]
              lapply (fv_to_in_term) * #Ht #_ @bool_impl_inv2 @Ht ]
            normalize cases fvb_e normalize [ >if_monotone #abs destruct ]
            cases fvb_b normalize //
          ]
          >iper_concat_lemma
          [ 2: >dom_push normalize >neqb_false >if_f lapply (Hbound1 m)
            cases domb_e // #HH @False_ind lapply (HH (refl …)) @le_Sn_n ]
            >push_lemma whd in match (match ? in Substitution with [_⇒?]);
            >atomic_subst >push_lemma
            whd in match (match ? in Substitution with [_⇒?]);
            >atomic_subst normalize @or_introl % // lapply fvb_tcterm * #Ht #_
            @Ht cut (fvb y 〈b, e〉= false)
              [ <H411
                [ 2: change with (max ? ?≤n) @(transitive_le … (le_maxl … Hm) Hsn)
                | lapply Hldom2 cases y #ny #Hldom2' lapply (Hldom2' ny)
                  >domb_concat_distr >dom_push whd in match (domb_e ? (Cons ? ?));
                  whd in match (veqb ? ?); >neqb_refl #HH cut (s ≤ny)
                  [ @HH normalize >if_monotone @refl ] -HH #Hsny
                  lapply (transitive_le … (le_maxl … Hm) Hsny)
                  change with (fresh_var_t (appl ? ?)) in match (max ? ?);
                  #Hfv cut (inb_t (νny) (appl r1 r2)= false)
                  [ lapply Hfv lapply (fresh_var_to_in) * #Ht #_ @Ht ]
                  @bool_impl_inv2 lapply (fv_to_in_term) * #Ht #_ @Ht
                ]
              | @bool_impl_inv2 lapply (fv_lemma) * * * * #Hc #_ #_ #_ #_
                change with (read_back 〈b, e〉)
                  in match (aux_read_back (read_back_b ?) ?);
                @Hc
              ]
          | *
            [ 2: * #Ha #Hb destruct >aux_read_back1
              change with (pif_subst ? ?) in match (aux_read_back ? ?);
              change with (pif_subst ? ?) in match (aux_read_back ? (Cons ??));
              >push_lemma
              whd in match (match ? in Substitution with [_⇒?]);
              >push_lemma
              whd in match (match ? in Substitution with [_⇒?]); >atomic_subst
              >no_subst
              [ 2: change with (neqb ? ? = false) >neq_simm >neqb_false @refl ]
              >(pre_iper_concat_lemma e (val_to_term (pvar νm)))
              [ 2: #k normalize
                cut (veqb k (νm)= true ∨ veqb k (νm)= false) // * #Hkm >Hkm
                normalize
                [ #_ elim (veqb_true_to_eq k (νm)) #Heq lapply (Heq Hkm) -Heq
                  #Hkm destruct #_ lapply (Hbound1 m) cases domb_e // #HH
                  @False_ind lapply (HH (refl …)) @le_Sn_n
                | #abs destruct
                ] ]
              >atomic_subst >no_subst5
              [ 2: change with (read_back 〈b, e〉) in match (aux_read_back (read_back_b ?) ?);
                cut (fvb (νm) 〈b, e〉= false)
                [ cut (fvb_b (νm) b = false)
                  [ cut (inb_b (νm) b = false)
                    [ lapply (le_maxl … (Hline1 (transitive_le … (le_maxl … Hm) Hsn)))
                      lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
                      @Hb ]
                    @bool_impl_inv2 lapply (fv_to_in_crumble) * * * * #_ #Hb
                    #_ #_ #_ @Hb ]
                  cut (fvb_e (νm) e = false)
                  [ cut (inb_e (νm) e = false)
                    [ lapply (le_maxr … (Hline1 (transitive_le … (le_maxl … Hm) Hsn)))
                      lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
                      @He ]
                    @bool_impl_inv2 lapply (fv_to_in_crumble) * * * * #_ #_
                    #He #_ #_ @He ]
                   #He #Hb normalize >He >Hb normalize @refl ]
                @bool_impl_inv2 lapply fv_lemma * * * * #Hc #_ #_ #_ #_ @Hc ]
              lapply (H2' 〈B, E〉 (crc b1 (envc Epsilon y)) (le_maxr … Hm))
              whd in match (match ? in CrumbleContext with [_⇒?]);
              whd in match (plug_c ? ?);
              whd in match (plug_e ? ?); >concat_to_push #H22
              lapply (H22 (refl …)) -H22 whd in match (aux_read_back ? Epsilon);
              whd in match (hole_subst (appl ? ?) ?);
              whd in match (rv_context (c_appl ? ?)); #H22 @or_introl % //
              lapply fvb_tcterm * #Ht #_ @Ht
              change with (read_back 〈b, e〉) in match (aux_read_back (read_back_b ?) ?);
              cut (fvb y 〈b, e〉= false)
              [ <H411 [ 2: change with (max ? ?≤n)
                @(transitive_le … (le_maxl … Hm)Hsn) ]
                cut (inb_t y (appl r1 r2) = false)
                [ lapply Hldom2 cases y #ny -Hldom2 #Hldom2
                  lapply (Hldom2 ny) >dom_push whd in match (domb_e ? ?);
                  whd in match (veqb ? ?); >neqb_refl >if_t #HH
                  lapply (transitive_le … (le_maxl … Hm) (HH (refl …)))
                  change with (fresh_var_t (appl ? ?)) in match (max ? ?);
                  lapply (fresh_var_to_in) * #Ht #_ @Ht ]
                @bool_impl_inv2 lapply (fv_to_in_term) * #Ht #_ @Ht ]
              lapply fv_lemma * * * * #Hc #_ #_ #_ #_ @bool_impl_inv2 @Hc ]
            *
            [ 2: * * #Ha #Hb #Hc destruct >aux_read_back1
              >push_lemma
              whd in match (match ?  in Substitution with [_⇒?]);
              >push_lemma
              whd in match (match ?  in Substitution with [_⇒?]);
              >atomic_subst >no_subst
              [ 2: change with (neqb ? ? = false) >neq_simm @neqb_false ]
              >(pre_iper_concat_lemma e (val_to_term (pvar (νm))))
              [ 2: * #k normalize cut (neqb k m = true ∨ neqb k m = false) // * #Hkm
                >Hkm normalize [ 2: #abs destruct ]
                elim (neqb_iff_eq k m) #Heq #_ lapply (Heq Hkm) -Heq #Heq
                destruct #_ lapply (Hbound1 m) cases domb_e //
                #HH @False_ind lapply (HH (refl …)) @le_Sn_n ]
              normalize >neqb_refl >if_t @or_introl % //
              lapply (fvb_tcterm) * #Ht #_ @Ht
              cut (fvb (νm) 〈b, e〉= false)
                [ cut (fvb_b (νm) b = false)
                  [ cut (inb_b (νm) b = false)
                    [ lapply (le_maxl … (Hline1 (transitive_le … (le_maxl … Hm) Hsn)))
                      lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
                      @Hb ]
                    @bool_impl_inv2 lapply (fv_to_in_crumble) * * * * #_ #Hb
                    #_ #_ #_ @Hb ]
                  cut (fvb_e (νm) e = false)
                  [ cut (inb_e (νm) e = false)
                    [ lapply (le_maxr … (Hline1 (transitive_le … (le_maxl … Hm) Hsn)))
                      lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
                      @He ]
                    @bool_impl_inv2 lapply (fv_to_in_crumble) * * * * #_ #_
                    #He #_ #_ @He ]
                   #He #Hb normalize >He >Hb normalize @refl ]
              lapply fv_lemma * * * * #Hc #_ #_ #_ #_
              @bool_impl_inv2
              change with (read_back 〈b, e〉) 
                in match (aux_read_back (read_back_b b) e); @Hc
              ]
           *
          [ * * #Ha #Hb #Hc destruct normalize >neqb_refl >neqb_false normalize
            @or_intror % //
          | * #x * #z * * #Ha #Hb #Hc destruct >aux_read_back1 >push_lemma
            whd in match (match ? in Substitution with [_⇒?]);  >push_lemma
            whd in match (match ? in Substitution with [_⇒?]); >atomic_subst
            >no_subst [ 2: change with (neqb ? ?=false) >neq_simm @neqb_false ]
            lapply (H1' 〈B, z〉 (crc b (envc x y)) (transitive_le … (le_maxl … Hm) Hsn))
            whd in match (plug_c ? ?);
            whd in match (plug_e ? ?); #H11 lapply (H11 (refl …)) -H11
            whd in match (match ? in CrumbleContext with [_⇒?]); #H11
            normalize @or_intror % //
            >pre_iper_concat_lemma
            [ 2: * #k normalize cut (neqb k m = true ∨ neqb k m = false) // * #Hkm
              >Hkm normalize [ 2: #abs destruct ] #_
              elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq #Heq destruct
              lapply (Hbound1 m) >domb_concat_distr normalize cases domb_e //
              >if_monotone >if_t #HH @False_ind lapply (HH (refl …)) @le_Sn_n ]
            lapply tc_lemma * #_ #Hv @Hv normalize
            cut (veqb y (νm) = true ∨ veqb y (νm) = false) // * #Hym >Hym //
            elim (veqb_true_to_eq y νm) #Heq #_ lapply (Heq Hym) -Heq #Heq
            destruct lapply (Hbound1 m)
            >domb_concat_distr normalize >neqb_refl normalize #HH @False_ind
            lapply (HH (refl …)) @le_Sn_n
        ]
      ]
    ]
  ]
] qed.

lemma fv_plug_aux1: ∀m, vv, b, e, l.
 ∀(H' : (max (max (S m) (fresh_var_v vv)) (fresh_var_e (push e [νm←b]))≤l)).
  (fresh_var (plug_c (crc (AppValue (var νm) vv) (envc Epsilon νm)) 〈b,e〉)≤l). 

#m #vv #b #e #l #H'
>fresh_var_over_plug
       change with (max ? ?) in match (fresh_var_cc ?);
       change with (max ? ?) in match (fresh_var_b ?);
       change with (S m) in match (fresh_var_v ?);
       change with (max ? ?) in match (fresh_var ?);
       lapply H'
       <(fresh_var_push … [νm←b])
       change with (max ? ?) in match (fresh_var_e ?);
       change with (max ? ?) in match (fresh_var_s ?);
       #H' @to_max
       [ @to_max
         [ @(le_maxl … H') | @(le_maxl … (le_maxl … H')) ]
       | @to_max
         [ @((le_maxr … (le_maxr … (le_maxr … H')))) |@(le_maxl … (le_maxr … H')) ]
       ]
qed.

lemma fv_plug_aux2: ∀m, vv, b1, e1, l.∀(H': (max (max (fresh_var_v vv) (S m)) (fresh_var_e (push e1 [νm←b1]))≤l)).
     (fresh_var (plug_c (crc (AppValue vv (var νm)) (envc Epsilon νm)) 〈b1,e1〉)≤l).

#m #vv #b #e #l #H'
>fresh_var_over_plug
change with (max ? ?) in match (fresh_var_cc ?);
change with (max ? ?) in match (fresh_var_b ?);
change with (S m) in match (fresh_var_ec ?);
change with (S m) in match (fresh_var_v (var ?));
change with (max ? ?) in match (fresh_var ?);
@to_max
[ @to_max
  [ @(le_maxl … H') | @(le_maxr … (le_maxl … H')) ]
| <fresh_var_push in H'; change with (max ? (max ? ?)) in match (fresh_var_e ?);
  #H' @to_max
  [ @(le_maxr … (le_maxr … (le_maxr … H'))) | @(le_maxl … (le_maxr … H')) ]
] qed.

lemma eq_Sn_n: ∀n. S n= n → False.
@nat_ind [ #abs destruct ] #n #H #H'' @H // qed.

lemma plug_decomposition: 
∀f1, f2, b1, e1, y1, b1', b2, e2, y2, b2'.
 plug_c (crc b1 (envc e1 y1)) 〈b1', f1〉 = plug_c (crc b2 (envc e2 y2)) 〈b2', f2〉 → 
  b1 = b2 ∧ 
  ( (e1 = e2 ∧ y1 = y2 ∧ b1' = b2' ∧ f1 = f2) ∨
   (∃x. e1 = concat (Cons e2 [y2←b2']) x ∧ f2 = (concat (Cons x [y1←b1']) f1)) ∨
   (∃x. e2 = concat (Cons e1 [y1←b1']) x ∧ f1 = (concat (Cons x [y2←b2']) f2))).
@Environment_double_ind2
[ normalize #b1 #e1 #y1 #b1' #b2 #e2 #y2 #b2' #Heq destruct % // % % % % % //
| normalize #f1 #s1 #b1 #e1 #y1 #b1' #b2 #e2 #y2 #b2' #Heq destruct % // @or_intror
  % [ @f1 ] % @refl
| normalize #f1 #s1 #b1 #e1 #y1 #b1' #b2 #e2 #y2 #b2' #Heq destruct % // @or_introl
  @or_intror % [ @f1 ] % @refl
| normalize #f1 #f2 #s1 #s2 #HI #b1 #e1 #y1 #b1' #b2 #e2 #y2 #b2' #Heq
  cut (CCrumble b1 (concat (Cons e1 [y1←b1']) f1)=〈b2,concat (Cons e2 [y2←b2']) f2〉 ∧ 
       b1 = b2 ∧ s1 = s2)
  [ lapply Heq generalize in match ((concat (Cons e1 [y1←b1']) f1)); #cc
    generalize in match (concat (Cons e2 [y2←b2']) f2); #dd -Heq #Heq destruct 
    % % @refl ] * * -Heq #Heq #Hb #Hs destruct
    lapply (HI … Heq) * #Hb #HH destruct % // elim HH
    [ 2: * #x * #Ha #Hb @or_intror % [ @x ] % //
    | *
      [ 2: * #x * #Ha #Hb @or_introl @or_intror % [ @x ] % //
      |  * * * #Ha #Hb #Hc #Hd destruct @or_introl @or_introl  % % % %
      ]
    ]
] qed.

definition pi1c ≝ λc. match c with [CCrumble b e ⇒ b].
definition pi2c ≝ λc. match c with [CCrumble b e ⇒ e]. 

lemma plug_decomposition2: 
∀ b1, e1, y1, c1, b2, e2, y2, c2.
 plug_c (crc b1 (envc e1 y1)) c1 = plug_c (crc b2 (envc e2 y2)) c2 → 
  b1 = b2 ∧ 
  ( (e1 = e2 ∧ y1 = y2 ∧ pi1c c1=pi1c c2 ∧ pi2c c1=pi2c c2) ∨
   (∃x. e1 = concat (Cons e2 [y2←pi1c c2]) x ∧ pi2c c2 = (concat (Cons x [y1←pi1c c1]) (pi2c c1))) ∨
   (∃x. e2 = concat (Cons e1 [y1←pi1c c1]) x ∧ pi2c c1 = (concat (Cons x [y2←pi1c c2]) (pi2c c2)))).

#b1 #e1 #y1 * #b1' #f1 #b2 #e2 #y2 * #b2' #f2 @plug_decomposition qed.

lemma plug_c_to_eq: ∀b ,e ,y , c,b' ,e' ,y' , c'.
 e_len e = e_len e' →
  plug_c (crc b (envc e y)) c = plug_c (crc b' (envc e' y')) c' → 
   b = b' ∧ e = e' ∧ y = y' ∧ c=c'.
#b #e #y * #bb #ee #b' #e' #y' * #bb' #ee' #H normalize #H destruct
lapply e0 -H lapply H
 @(Environment_double_ind2 … ee ee')
[ normalize #_ #H' destruct % // % // % //
| #e1 #s cut (e_len (concat (Cons e [y←bb]) (Cons e1 s)) ≠ e_len (concat (Cons e' [y'←bb']) Epsilon))
  [ >concat_len >concat_len normalize >H % <plus_n_Sm #abs destruct
    cut (∀n. n+0=n) // #Hn lapply e2 >Hn /3/ ] #Hneq #Hlen #Heq
  cut (e_len (concat (Cons e [y←bb]) (Cons e1 s)) = e_len (concat (Cons e' [y'←bb']) Epsilon))
  [ @e_len_lemma @Heq ] #Hlen
  @False_ind @(absurd … Hlen Hneq)
| #e1 #s normalize cut (e_len (Cons e [y←bb])≠e_len (Cons (concat (Cons e' [y'←bb']) e1) s))
  [ normalize >concat_len normalize >H %  /3/ ] #Hneq #Hlen #Heq
    cut (e_len (Cons e [y←bb])=e_len (Cons (concat (Cons e' [y'←bb']) e1) s))
  [ @e_len_lemma @Heq ] #Hlen
  @False_ind @(absurd … Hlen Hneq)
| #E #f #se #sf #HI #H normalize #HH cut (se=sf)
  [ lapply HH generalize in match (concat ? ?); #xx
    generalize in match (concat ? ?); #yy -HH #HH destruct // ]
  #H1 destruct lapply (HI H e1) * * * * #a #d #c -H destruct % // % // % //
] qed.

lemma gamma_epsilon: ∀l, H. pi1 … (gamma_e Epsilon l H) = Epsilon.
@list_ind
[ //
| * #y #y' #tl #HI #J whd in match (gamma_e ? ? ?);
  cut (∀H1, H2. sse (pi1 … (gamma_e Epsilon tl H1)) y y' H2 = Epsilon)
  [ 2: #UU @UU ]
   >HI [ // ] % // elim J #_ normalize * //
] qed.

lemma gamma_btovl: ∀v, w, l.∀ (H : ((∀x:Variable.rhs l x→inb_b x (AppValue v w)=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→inb_v x v=false)∧distinct_rhs l).
#v #w #l #H %
[ #k #Ha elim H #Hb #_ lapply (Hb k) normalize elim (inb_v k v) normalize // #Hc
  @Hc @Ha
| elim H #_ #HH @HH
] qed.

lemma gamma_btovr: ∀v, w, l.∀ (H : ((∀x:Variable.rhs l x→inb_b x (AppValue v w)=false)∧distinct_rhs l)).
 ((∀x:Variable.rhs l x→inb_v x w=false)∧distinct_rhs l).
#v #w #l #H %
[ #k #Ha elim H #Hb #_ lapply (Hb k) normalize elim (inb_v k w) // >if_monotone #Hc
  @Hc @Ha
| elim H #_ #HH @HH
] qed.
(*
lemma concat_gamma_semplification1: ∀f, e, x, b, l, H. 
 pi1 … (gamma_var (νx) (beta_e (concat e (push f [νx←b])) l) H) = (ν(l+ e_len f)).
@Environment_simple_ind2
[ #e #x #b #l
   whd in match (push ? ?);  whd in match (concat ? ?);
   >concat_e_epsilon whd in match (e_len ?); whd in match (beta_e ? ?);
   #H whd in match (gamma_var ? ? ?);
*)
 
lemma gamma_distro: ∀l, v, w, H. pi1 … (gamma_b (AppValue v w) l H) =
 AppValue (pi1 … (gamma_v v l (gamma_btovl … H))) (pi1 … (gamma_v w l (gamma_btovr … H))).  
@list_ind // * #y #y' #tl #HI #v #w #H
whd in match (gamma_b ? ? ?);
whd in match (gamma_v ? ? ?);
whd in match (gamma_v w ? ?);
generalize in match (gamma_v_aux3 ? ? ? ? ? ?);
generalize in match (gamma_v_aux3 ? ? ? ? ? ?);
generalize in match (gamma_v_aux2 ? ? ? ?);
generalize in match (gamma_v_aux2 ? ? ? ?);
generalize in match (gamma_b_aux2 ? ? ? ?);
generalize in match (gamma_b_aux3 ? ? ? ? ? ?);
>HI
#P1 #P2 #P3 #P4 #P5 #P6
whd in match (ssb ? ? ? ?); // qed.

lemma gamma_var_simplification1: ∀f, e, x, b, l, H.
 domb_e x f = false → domb_e x e = false → 
  fresh_var_e (concat e (push f [x←b])) ≤ l → 
 pi1 … (gamma_var x (beta_e (concat e (push f [x←b])) l) H) = ν(l+e_len f).
@Environment_simple_ind2
[ #e #x #b #l whd in match (push ? ?); whd in match (concat ? ?);
  >concat_e_epsilon #H #_ #H1 whd in match (beta_e ? ?);
  whd in match (gamma_var ? ? ?);
  >gamma_var_ns // >veqb_true whd in match (e_len ?);
  cut (l+0=l) // #HH >HH //
| #f * #z #b' #HI #e #x #b #l whd in match (push ? ?);
  whd in match (concat ? ?); #H
  whd in match (beta_e ? ?);
  whd in match (gamma_var ? ? ?); #H1 #H2 #H3 >HI
  [ 2: >fresh_var_concat lapply H3
    change with (max ? ?) in match (fresh_var_e ?);
    >fresh_var_concat -H3 #H3 @to_max
    [ @le_S @(le_maxl … (le_maxl … H3))
    | @le_S @(le_maxr … (le_maxl … H3))
    ]
  | 3: @H2
  | 4: lapply H1 normalize cases domb_e // >if_monotone #H @H
  ]
  cut (veqb (ν(S l+e_len f)) z = true ∨ veqb (ν(S l+e_len f)) z = false) // *
  #Hveq >Hveq whd in match (e_len (Cons ? ?)); <plus_n_Sm //
  elim (veqb_true_to_eq (ν(S l+e_len f)) z) #Heq #_ lapply (Heq Hveq) -Heq #Heq
  destruct @False_ind lapply H3
  change with (max ? (max ? ?)) in match (fresh_var_e ?); -H3 #H3
  lapply (le_maxl … (le_maxr … H3)) cut (l ≤ (S l+ e_len f)) [//] /2/
] qed.

lemma gamma_var_simplification2: ∀e, f, x, b, l, H.
 domb_e x f = false → domb_e x e = false → 
  fresh_var_e (concat e (push f [x←b])) ≤ l → 
 pi1 … (gamma_var x (beta_e (concat (push f [x←b]) e) l) H) = ν(l+e_len e+e_len f).
@Environment_simple_ind2
[ #f #x #b #l #H #H1 #_ #H2
  cut (concat (push f [x←b]) Epsilon = concat Epsilon (push f [x←b])) //
  #Heq generalize in match H; >Heq #A
  lapply (gamma_var_simplification1 (f) Epsilon x b l A H1 (refl …) H2)
  whd in match (e_len Epsilon); #HH >HH /2/
| #f * #z #b' #HI #e #x #b #l whd in match (push ? ?);
  whd in match (concat ? ?); #H
  whd in match (beta_e ? ?);
  whd in match (gamma_var ? ? ?); #H1 #H2 #H3 >HI
  [ 2: lapply H3 >fresh_var_concat >fresh_var_concat
    change with (max ? ?) in match (fresh_var_e ?); -H3 #H3
    @to_max [ @(le_S … (le_maxl … (le_maxl … H3))) | @(le_S … (le_maxr … H3)) ]
  | 3: lapply H2 normalize cases domb_e // >if_monotone #H @H
  | 4: @H1
  ]
  cut (veqb (ν(S l+e_len f+e_len e)) z = true ∨ veqb (ν(S l+e_len f+e_len e)) z = false) // *
  [ 2: #Heq >Heq >if_f normalize <plus_n_Sm /2/
  | #Hveqb elim (veqb_true_to_eq (ν(S l+e_len f+e_len e)) z) #Heq #_ lapply (Heq Hveqb) -Heq
    #Heqw destruct @False_ind lapply H3 >fresh_var_concat
    change with (max ? (max ? ?)) in match (fresh_var_e ?); -H3 #H3
    lapply (le_maxl … (le_maxr … (le_maxl … H3))) /2/
  ]
] qed.

lemma rhs_beta_concat_distro1: ∀f, e, x, l. rhs (beta_e (concat e f) l) x → (rhs (beta_e e (l+e_len f)) x ∨ rhs  (beta_e f (l)) x).
@Environment_simple_ind2
[ #e #x #l normalize #H @or_introl // 
| #f *#y #b #HI #e #x #l normalize *
  [ #HH elim (veqb_true_to_eq … x νl) #Heq #_ lapply (Heq HH) *
    @or_intror @or_introl @veqb_true
  | #H elim (HI e x (S l) H)
    [ #HI  @or_introl <plus_n_Sm @HI
    | #HI @or_intror @or_intror @HI
    ]
  ]
] qed.

lemma rhs_beta_concat_distro2: ∀f, e, x, l. (rhs (beta_e e (l+e_len f)) x ∨ rhs  (beta_e f (l)) x) →  rhs (beta_e (concat e f) l) x.
@Environment_simple_ind2
[ #e #x #l normalize * // #H @False_ind @H 
| #f * #y #b #HI #e #x #l normalize *
  [ #HH @or_intror @HI @or_introl //
  | * #HH 
    [ @or_introl @HH
    | @or_intror @HI @or_intror @HH
    ]
  ]
] qed.

lemma in_gamma_e: ∀l, e, x, H. 
 (inb_e x e) = false →
  (¬rhs l x ) →   
   inb_e x (pi1 … (gamma_e e l H)) = false.
@list_ind
[ #e #x #H normalize #H1 #_ @H1
| * #y #y' #tl #HI #e #x #H #H1 #H2
  whd in match (gamma_e ? ? ?);
  lapply alpha_fin1 * * * * #_ #_ #He #_ #_ >He [ @refl]
  [ 2: @HI // % #Hk elim (H2) #H2 @H2 normalize @or_intror @Hk
  | elim H2 normalize >veqb_comm cases veqb // #HH @False_ind @HH @or_introl //
  ]
] qed. 

lemma gammae_concat_irrelevance: ∀f, e, l, t, H.
 (∀x. domb_e x f = true → inb_e x e = false ∧ inb_e x t = false) →
  fresh_var_e (concat e f) ≤ l →
  pi1 … (gamma_e t (beta_e (concat e f) l) H) = pi1 … (gamma_e t (beta_e e (l+e_len f)) ?). 
[ 2: % // #k #Hk elim H #H' #_ @H' @rhs_beta_concat_distro2 @or_introl @Hk ]
@Environment_simple_ind2
[ #e #l #t whd in match (concat ? ?); whd in match (e_len ?); #H
  generalize in match ( conj ? ? ? ?);
  generalize in match H; cut (l+0=l) // #HH >HH //
| #f * * #y #b #HI #e #l #t
  whd in match (concat ? ?);
  whd in match (beta_e ? ?); #H
  whd in match (gamma_e ? ? ?); #HH #H2
  generalize in match (gamma_e_aux3 ? ? ? ? ? ?);
  generalize in match (gamma_e_aux2 ? ? ? ?);
  generalize in match (conj ? 
   (distinct_rhs (beta_e e (l+e_len (Cons f [νy←b])))) ? ?); 
  generalize in match H;
   whd in match (e_len (Cons ? ?)); <plus_n_Sm
  #P1 #P2 #P3 >HI
  [ 2: @(le_S … (le_maxl … H2)) 
  | 3: #k #Hk @HH normalize >Hk >if_monotone @refl] #P4
   lapply ssc_in * * * * #_ #_ #He #_ #_ >He [ // ]
   >in_gamma_e
   [ @refl
   | 3: elim (HH (νy) ?) // normalize >neqb_refl //
   | % #Hy elim (betae_rhs_bound … Hy) #Ha #_ @False_ind
     lapply (transitive_le … (le_S … Ha) (le_maxl … (le_maxr … H2))) /2/
   ]
] qed.


lemma gamma_e_irrelevance: ∀f, l, t, H.
 (∀x. domb_e x f = true →  inb_e x t = false) →
  fresh_var_e f ≤ l →
  pi1 … (gamma_e t (beta_e f l) H) = t .
@Environment_simple_ind2
[ #l whd in match (beta_e ? ?); #t whd in match (gamma_e ? ? ?); // % // #k
  normalize #abs @False_ind @abs
| #e * * #y #b #HI #l #t #H1 #H2 #H3
  whd in match (beta_e ? ?);
  whd in match (gamma_e ? ? ?);
  generalize in match (gamma_e_aux3 ? ? ? ? ? ?); >HI
  [ 2: @(le_S … (le_maxl … H3))
  | 3: * #k #Hk @H2 normalize >Hk >if_monotone @refl
  ]
  #aa lapply ssc_in * * * * #_ #_ #He #_ #_ @He @H2 normalize >neqb_refl @refl
] qed.  


lemma in_gamma_b: ∀l, e, x, H. 
 (inb_b x e) = false →
  (¬rhs l x ) →   
   inb_b x (pi1 … (gamma_b e l H)) = false.
@list_ind
[ #e #x #H normalize #H1 #_ @H1
| * #y #y' #tl #HI #e #x #H #H1 #H2
  whd in match (gamma_e ? ? ?);
  lapply alpha_fin1 * * * * #_ #He #_ #_ #_ >He [ @refl]
  [ 2: @HI // % #Hk elim (H2) #H2 @H2 normalize @or_intror @Hk
  | elim H2 normalize >veqb_comm cases veqb // #HH @False_ind @HH @or_introl //
  ]
] qed. 


lemma gammab_concat_irrelevance: ∀f, e, l, t, H.
 (∀x. domb_e x f = true → inb_e x e = false ∧ inb_b x t = false) →
  fresh_var_e (concat e f) ≤ l →
  pi1 … (gamma_b t (beta_e (concat e f) l) H) = pi1 … (gamma_b t (beta_e e (l+e_len f)) ?). 
[ 2: % // #k #Hk elim H #H' #_ @H' @rhs_beta_concat_distro2 @or_introl @Hk ]
@Environment_simple_ind2
[ #e #l #t whd in match (concat ? ?); whd in match (e_len ?); #H
  generalize in match ( conj ? ? ? ?);
  generalize in match H; cut (l+0=l) // #HH >HH //
| #f * * #y #b #HI #e #l #t
  whd in match (concat ? ?);
  whd in match (beta_e ? ?); #H
  whd in match (gamma_b ? ? ?); #HH #H2
  generalize in match (gamma_b_aux3 ? ? ? ? ? ?);
  generalize in match (gamma_b_aux2 ? ? ? ?);
  generalize in match (conj ? 
   (distinct_rhs (beta_e e (l+e_len (Cons f [νy←b])))) ? ?); 
  generalize in match H;
   whd in match (e_len (Cons ? ?)); <plus_n_Sm
  #P1 #P2 #P3 >HI
  [ 2: @(le_S … (le_maxl … H2)) 
  | 3: #k #Hk @HH normalize >Hk >if_monotone @refl] #P4
   lapply ssc_in * * * * #_ #Hb #_ #_ #_ >Hb [ // ]
   >in_gamma_b
   [ @refl
   | 3: elim (HH (νy) ?) // normalize >neqb_refl //
   | % #Hy elim (betae_rhs_bound … Hy) #Ha #_ @False_ind
     lapply (transitive_le … (le_S … Ha) (le_maxl … (le_maxr … H2))) /2/
   ]
] qed.

lemma in_gamma_v: ∀l, e, x, H. 
 (inb_v x e) = false →
  (¬rhs l x ) →   
   inb_v x (pi1 … (gamma_v e l H)) = false.
@list_ind
[ #e #x #H normalize #H1 #_ @H1
| * #y #y' #tl #HI #e #x #H #H1 #H2
  whd in match (gamma_e ? ? ?);
  lapply alpha_fin1 * * * * #_ #_ #_ #He #_ >He [ @refl]
  [ 2: @HI // % #Hk elim (H2) #H2 @H2 normalize @or_intror @Hk
  | elim H2 normalize >veqb_comm cases veqb // #HH @False_ind @HH @or_introl //
  ]
] qed. 

lemma gammav_concat_irrelevance: ∀f, e, l, t, H.
 (∀x. domb_e x f = true → inb_e x e = false ∧ inb_v x t = false) →
  fresh_var_e (concat e f) ≤ l →
  pi1 … (gamma_v t (beta_e (concat e f) l) H) = pi1 … (gamma_v t (beta_e e (l+e_len f)) ?). 
[ 2: % // #k #Hk elim H #H' #_ @H' @rhs_beta_concat_distro2 @or_introl @Hk ]
@Environment_simple_ind2
[ #e #l #t whd in match (concat ? ?); whd in match (e_len ?); #H
  generalize in match ( conj ? ? ? ?);
  generalize in match H; cut (l+0=l) // #HH >HH //
| #f * * #y #b #HI #e #l #t
  whd in match (concat ? ?);
  whd in match (beta_e ? ?); #H
  whd in match (gamma_v ? ? ?); #HH #H2
  generalize in match (gamma_v_aux3 ? ? ? ? ? ?);
  generalize in match (gamma_v_aux2 ? ? ? ?);
  generalize in match (conj ? 
   (distinct_rhs (beta_e e (l+e_len (Cons f [νy←b])))) ? ?); 
  generalize in match H;
   whd in match (e_len (Cons ? ?)); <plus_n_Sm
  #P1 #P2 #P3 >HI
  [ 2: @(le_S … (le_maxl … H2)) 
  | 3: #k #Hk @HH normalize >Hk >if_monotone @refl] #P4
   lapply ssc_in * * * * #_ #_ #_ #Hb #_ >Hb [ // ]
   >in_gamma_v
   [ @refl
   | 3: elim (HH (νy) ?) // normalize >neqb_refl //
   | % #Hy elim (betae_rhs_bound … Hy) #Ha #_ @False_ind
     lapply (transitive_le … (le_S … Ha) (le_maxl … (le_maxr … H2))) /2/
   ]
] qed.

lemma gamma_b_to_v: ∀l, v, H. pi1 … (gamma_b (CValue v) l H) = CValue (pi1 … (gamma_v v l H)).
@list_ind
[ normalize //
| * #y #y' #tl #HI #v #H
  whd in match (gamma_b ? ? ?);
  whd in match (gamma_v ? ? ?);
  generalize in match (gamma_b_aux3 … H); 
  generalize in match (gamma_v_aux3 … H); >HI #P1 #P2
  whd in match (ssb ? ? ? ?); @eq_f //
] qed.

lemma inb_alphae_false1: 
∀e, k, l, H. l > k → inb_e (νk) e = false → inb_e (νk) (pi1 … (alpha_e e l H)) = false.
@Environment_simple_ind2
[ #k #l #H #H1 #_ normalize @refl
| #e * * #y #b #HI #k #l #H1 #H2 #H3 whd in match (alpha_e ? ? ?);
  lapply (HI k (S l) (alpha_e_aux3 l e (νy) b H1) (le_S … H2) ?)
  [ lapply (orb_false … H3) * // ]
  cases (alpha_e) #aa #hh whd in match (match ? in Sig with [_⇒?]);
  whd in match (inb_e ? (Cons ? ?));
  whd in match (inb_s ? ?); elim ((orb_false … H3)) #_ #H3
  elim ((orb_false … H3)) #_ #H3 >H3 -H3
  whd in match (veqb ? ?);
  cut (neqb k l = true ∨ neqb k l = false) // *
  [ #Hkl elim (neqb_iff_eq … k l) #Heq #_ lapply (Heq Hkl) -Heq #Heq
    -H3 destruct @False_ind lapply H2 @le_Sn_n ]
  #Hkl >Hkl >if_f >if_then_true_else_false
  lapply alpha_fin1 * * * * #_ #_ #He #_ #_ #HH @He //
] qed.

lemma alpha_push_aux1: ∀e,y,b,n. ∀(H : (fresh_var_e (push e [y←b])≤n)).
 (fresh_var_e e≤n).
#e #y #b #n <fresh_var_push #H @(le_maxl … H) qed.

lemma alpha_push_aux2: ∀e,y,b,n. ∀(H : (fresh_var_e (push e [y←b])≤n)).
((∀x:Variable.rhs (beta_e e n) x→inb_b x b=false)∧distinct_rhs (beta_e e n)).

#e * #y #b #n <fresh_var_push #H % // * #k #Hk elim (betae_rhs_bound … Hk) -Hk #Hk #_
change with (max ? (max ? ?)≤n) in H; lapply (transitive_le … (le_maxr … (le_maxr … H)) Hk)
lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb qed.

lemma sse_push_aux1: ∀y', e, s.  ∀(H : (inb_e y' (push e s)=false)).
 (inb_s y' s=false).
#y' #e #s >inb_push #H elim (orb_false … H) // qed. 

lemma sse_push_aux2: ∀y', e, s.  ∀(H : (inb_e y' (push e s)=false)).
 (inb_e y' e=false).
#y' #e #s >inb_push #H elim (orb_false … H) // qed. 


lemma sse_push: ∀e, s, y, y', H. sse (push e s) y y' H = concat (sse (Cons Epsilon s) y y' (sse_push_aux1 … H)) (sse e y y' (sse_push_aux2 … H)) .
@Environment_simple_ind2
[ * #z #b #y #y' #H
  whd in match (push ? ?); whd in match (sse ? ? ? ?);
  whd in match (sse Epsilon ? ? ?);
  whd in match (push ? ?); >concat_e_epsilon cases veqb //
| #e * #z' #b' #HI * #z #b #y #y' #H 
  whd in match (push ? ?); whd in match (sse (Cons ? ?) ? ? ?);
  whd in match (sse (Cons ? ?) ? ? ?);
  whd in match (sse (Cons ? ?) ? ? ?);
  >HI [ 2: whd in match (push ? ?) in H; elim (orb_false … H) // ]
  whd in match (sse (Cons ? ?) ? ? ?); cases veqb cases veqb //
] qed.

lemma e_len_push: ∀e, s. e_len (push e s) = S (e_len e).
@Environment_simple_ind2 // qed.

lemma alpha_push: ∀ e, y, b, n, H.
 pi1 … (alpha_e (push e [y←b]) n H) =push (pi1 … (alpha_e e n (alpha_push_aux1 … H))) 
  [ν(n+e_len e)←pi1 … (gamma_b b (beta_e e n) (alpha_push_aux2 … H))].
 @Environment_simple_ind2
 [ #y #b #n #H whd in match (push ? ?); whd in match (alpha_e ? ? ?);
   whd in match (sse ? ? ? ?); whd in match (beta_e ? ?);
   whd in match (push ? ?);  whd in match (e_len ?);
   whd in match (gamma_b b [] ?); //
 | #e * #z #b' #HI #y #b #n #H
   whd in match (push ? ?); whd in match (alpha_e ? ? ?);
   lapply (HI y b (S n) (alpha_e_aux3 n (push e [y←b]) z b' H))
   cases alpha_e #aa #hh
   whd in match (match ?  in Sig with [_⇒?]); #Heq destruct
   whd in match (alpha_e (Cons ? ?) ? ?);
   generalize in match (alpha_e_aux2 ? ? ? ? ? ? ?);
   generalize in match (alpha_push_aux1 ? ? ? ? ?);
   generalize in match (alpha_e_aux3 n e z b' ?);
   #P1 cases alpha_e #bb #jj #P2 #P3
   whd in match (match ?  in Sig with [_⇒?]);
   whd in match (push (Cons ? ?) ?); @eq_f2 //
   whd in match (beta_e (Cons ? ?) ?);
   whd in match (gamma_b ? (?::?) ?);
   >sse_push whd in match (sse (Cons ? ?) ? ? ?);
   cut (veqb z (ν(S n+e_len e)) = false)
   [ lapply H cases z #nz #HH lapply (le_maxl … (le_maxr … HH)) normalize
     cut (neqb nz (S (n+e_len e))=true ∨ neqb nz (S (n+e_len e))=false) // * //
     #Hnz elim (neqb_iff_eq … nz (S (n+e_len e))) #Heq #_ lapply (Heq Hnz) -Heq
     #Heq destruct #abs @False_ind
     lapply (le_S … (le_plus_a_r (e_len e) (S (S (n+e_len e))) n abs)) @le_Sn_n ]
     #Hf >Hf >if_f -Hf whd in match (sse ? ? ? ?); >concat_to_push
     whd in match (e_len (Cons ? ?)); <plus_n_Sm whd in match (plus ? ?);
     @eq_f2 //
 ]
qed.

lemma concat_same_len: ∀d,b,c,a. e_len b=e_len d → concat a b = concat c d → 
 a=c ∧ b = d.
@Environment_double_ind2
[ #c #a #_ normalize * % %
| 2, 3: #e #s #c #a normalize #abs destruct
| #e #f #s #t #HI #c #a normalize #H destruct #H1
  cut (concat a f = concat c e)
  [ lapply H1 generalize in match (concat ? ?);
    generalize in match (concat ? ?); #A #B #HH destruct @refl ]
    #e1 elim (HI c a e0 e1) * * %
  lapply H1 generalize in match (concat ? ?); generalize in match (concat ? ?);
  #A #B #HH destruct //
] qed.

lemma concat_same_len2: ∀d,b,c,a. e_len a=e_len c → concat a b = concat c d → 
 a=c ∧ b = d.
#d #b #c #a #HA #HB cut (e_len b=e_len d)
[ cut (e_len (concat a b)=e_len (concat c d)) [ >HB // ] >concat_len >concat_len
  >HA // -HA ] #H @concat_same_len // qed.

lemma sse_len: ∀e, y, y', H. e_len ((sse e y y' H))= e_len e.
@Environment_simple_ind2 //
#e * #y #b #HI #z #y' #H
whd in match (sse ? ? ? ?); cases veqb
[ >if_t normalize >HI // | >if_f normalize >HI // ]
qed. 

lemma alpha_e_len: ∀e, n, H. e_len (pi1 … (alpha_e e n H))= e_len e.
@Environment_simple_ind2 //
#e * #y #b #HI #n #H whd in match (alpha_e ? ? ?);
lapply (HI (S n) (alpha_e_aux3 n e y b H)) cases alpha_e #aa #hh
whd in match (match ? in Sig with [_⇒?]); whd in match (e_len (Cons ? ?));
>sse_len #H >H // qed.

lemma push_eq_concat: ∀g, e, f, s. push e s = concat f g →  
(∃x. push x s = f ∧ concat x g = e) ∨ f=Epsilon ∧ g= push e s.

@Environment_simple_ind2
[ #e #f #s normalize #h % % [@e] % //
| #g #sg #HI #e #f #s normalize
  cases f
  [ normalize >concat_epsilon_e #H @or_intror % //
  | #ff #sff normalize cases e normalize
    [ cases g
      [ normalize #HH destruct
      | #gg #sgg normalize #H destruct
      ] 
    | #gg #sgg #H cut ((push gg s) = concat (Cons ff sff) g)
      [ destruct // ] #Heq
      lapply (HI … Heq) *
        [ * #K * #Ha #Hb >Ha >Hb @or_introl
          % [ @K ] % //
          cut (sg = sgg)
          [ lapply H generalize in match (push ? ?);
            generalize in match (concat ? ?); #HH #C #P  destruct @refl ]
            * //
        | * #abs destruct
        ]
     ]
   ]
] qed.

lemma gamma_len: ∀l, e, H. e_len (pi1 … (gamma_e e l H)) = e_len e.
@list_ind // * #y #y' #tl #HI #e #H whd in match (gamma_e ? ? ?);
>sse_len @HI qed.

 lemma four_dot_five_dot_five_alpha: (∀t, s, c, C, l. ∀(Hm : (fresh_var_t t ≤ s)).
 ∀H'. 
 (pi1 Crumble ? (alpha_c (fst … (underline_pifTerm t s)) l H'))  = plug_c C c
   → rv_context (cc_read_back C) ) ∧
 (∀v:pifValue.True).

@pifValueTerm_ind 
[ #v #_ #s * #B #E #C #l normalize cases overline #v #n normalize
  cases C normalize // #b * #e #y #H #_
  whd in match (plug_c ? ?); 
  whd in match (plug_e ? ?);
  cases E [ normalize #H destruct ] #ee #ss normalize #H destruct
| 3: //
| 4: //
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply unerline_var_hole * #term_hole #value_hole
  lapply four_dot_one_dot_one * #H411t #H411v #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s #c #C #l
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?);
      cases (overline v1 s) #vv #n normalize
      cases (overline v2 n) #ww #m 
      #H2' #H1' cases C cases c #b #e normalize
      [ // ] #bb * #ee #y normalize cases e normalize
      [ #HH destruct
      | #ee #ss #abs destruct
      ]
    | #u1 #u2 normalize #H1 #H2 #s * #B #E *
      [ normalize change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
        cases underline_pifTerm * #bb #ee #nn normalize
        cases overline #vv #mm // ] #bb * #ee #y #l
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s)
      lapply (term_hole (appl u1 u2) s)
      lapply (Hbound (appl u1 u2) s)
      lapply (Hldom (appl u1 u2) s)
      lapply (Hmono1 (appl u1 u2) s)
      lapply (Hline1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      whd in match (match ? in Crumble with [_⇒?]);
      whd in match (match ? in Crumble with [_⇒?]);
      whd in match (match 〈b, e〉 in Crumble with [_⇒?]); normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hline1 #Hsn #Hldom1 #Hbound1 #Hvar_hole1 #H1'
      lapply (H2 n)
      lapply (value_hole v2 n)
      lapply (Hbound (val_to_term v2) n)
      lapply (Hldom (val_to_term v2) n) normalize
      lapply (Hmono2 v2 n)
      lapply (Hline2 v2 n)
      lapply (H411v v2 n)
      cases (overline v2 n) #vv #m #Hfvv2
      whd in match (match ? in Crumble with [_⇒?]); 
      whd in match (\fst ?);
      whd in match (\snd ?);
      #Hline2 #Hnm #Hldom2 #Hbound2 #Hvar_hole2 #H2' normalize
      change with (max (max (S ?) ?) ?) in match (if ? then ? else ?);
      #H' <alpha_c_to_alpha #Heq
      cut (pi1 … (alpha_c 〈AppValue (var νm) vv,push e [νm←b]〉 l H') =
      plug_c (crc bb (envc ee y)) 〈B,E〉) [ >Heq // ] -Heq #Heq
      cut (〈AppValue (var νm) vv,push e [νm←b]〉 =
       plug_c (crc (AppValue (var νm) vv) (envc Epsilon (νm))) 〈b, e〉)
      [ normalize >concat_to_push @refl ] #Heq'
      cut ((pi1 Crumble ? (alpha_c 〈AppValue (var νm) vv,push e [νm←b]〉 l H')) =
           (pi1 Crumble ? (alpha_c (plug_c (crc (AppValue (var νm) vv) (envc Epsilon νm)) 〈b,e〉) l ?)))
      [ @(fv_plug_aux1 … H')
      | cut (∀J, K. (pi1 Crumble ? (alpha_c 〈AppValue (var νm) vv,push e [νm←b]〉 l J)) =
           (pi1 Crumble ? (alpha_c (plug_c (crc (AppValue (var νm) vv) (envc Epsilon νm)) 〈b,e〉) l K)))
           [ 2: #UU @UU]  
        >Heq' #J #K @refl ] >Heq >gamma_lemma -Heq -Heq'
        whd in match (alpha_cc);
        whd in match (gamma_cc ? ? ?);
        whd in match (gamma_ec ? ? ?);
        #Heq lapply (plug_decomposition2 … Heq) * #Hbb *
        [ *
          [ * * * #Ha #Hb #Hc #Hd destruct whd in match (beta ? ?);
            whd in match (ssb ? ? ? ?);
            whd in match (ssv ? ? ? ?);
            whd in match (sse Epsilon ? ? ?);
            >gamma_epsilon
            cut (∀al5, gca1, gea3. (rv_context
  (hole_subst
   (aux_read_back
    (read_back_b
     (pi1 Byte ?
      (gamma_b
       (AppValue (if veqb (νm) (νm) then var (ν(l+e_len_c 〈b,e〉)) else var (νm) )
        (ssv vv (νm) (ν(l+e_len_c 〈b,e〉)) al5))
       (beta_e e l) gca1)))
    Epsilon)
   (pi1 Variable ?
    (gamma_var (ν(l+e_len_c 〈b,e〉)) (beta_e e l) gea3)))))
    [ 2: #uu @uu ] >veqb_true >if_t #al5 #gca1 #gea3    
     change with (read_back_b ?) 
       in match (aux_read_back (read_back_b (pi1 ? ? (gamma_b ? ? ?))) Epsilon);
       >gamma_distro
     whd in match (gamma_v (var ?) ? ?); >gamma_v_to_var
     whd in match (read_back_b ?); whd in match (hole_subst ? ?);
     whd in match (rv_context ?); @or_intror 
     whd in match (hole_subst ? ?);
     >veqb_true >if_t % // @tc_value_rb lapply fvb_tcterm * #Ht #_ @Ht
     lapply ssc_in * * * * #_ #_ #_ #Hv #_
     generalize in match (gamma_btovr ? ? ? ?); >Hv
     [ 2: lapply (Hline2 (transitive_le … (le_maxr … H) Hsn))
       lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
     #HtH >gamma_v_ns
       [ 2: * #k #Hk @(Hvar_hole2 … (transitive_le … (le_maxr … H)Hsn)
       (transitive_le … (le_maxr … H) (Hldom1 … Hk)) (Hbound1 … Hk) ) ]
     cut ((fvb_v (pi1 … (gamma_var (ν(l+e_len_c 〈b,e〉)) (beta_e e l) gea3)) vv
            =false))
     [ 2: lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @bool_impl_inv2 @Hv ] 
     >gamma_var_ns
     [ lapply (le_maxr … (le_maxl … H')) cut (l≤l+e_len_c 〈b,e〉) [ // ] #HH
       #Hmarco lapply (transitive_le … Hmarco HH) -HH -Hmarco #HH
       cut (inb_v (ν(l+e_len_c 〈b,e〉)) vv=false)
       [ lapply HH lapply fresh_var_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
       @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv 
     | cut ((∀x:ℕ.n≤x → domb_e (νx) e=false))
       [ #k lapply (Hbound1 k) cases domb_e // #HH #Ht @False_ind
         lapply (transitive_le … (HH (refl …)) Ht) @le_Sn_n ]
       #Hdom2' @Hdom2' cut (l≤l+e_len_c 〈b,e〉) [ // ] #HH
       @(transitive_le …
               (transitive_le … (le_S … Hnm) (le_maxl … (le_maxl … H'))) HH)
       ]
     ]
   | * #X
     whd in match (beta ? ?);
     whd in match (sse Epsilon ? ? ?);
     >gamma_epsilon * #abs @False_ind lapply abs
     cases X
     [ normalize #abs destruct
     | #XX #SS normalize #abs destruct
     ] ]
     * #X whd in match (beta ? ?);
     whd in match (sse Epsilon ? ? ?);
     >gamma_epsilon >concat_to_push
     whd in match (pi1c 〈B , E〉);
     whd in match (pi2c 〈B , E〉);  >alpha_be_to_gamma
     (*qui bisogna passare a gamma nell'ipotesi due*)  * 
     whd in match (pi1c ?); whd in match (pi2c ?);  #Ha #Hb
      lapply (alphae_domain_bound e l (alpha_to_gamma_aux11 b e l
     (gamma_lemma_aux1 〈b,e〉 (crc (AppValue (var νm) vv) (envc Epsilon νm)) l
      (fv_plug_aux1 m vv b e l H')))) >Hb #Hb'
       destruct
     whd in match (sse Epsilon ? ? ? );
     whd in match (ssb ? ? ? ?);
     whd in match (ssv ? ? ? ?);
     generalize in match (gamma_cc_aux1 ? ? ? ?);
     generalize in match (gamma_ec_aux2 ? ? ? ?); >veqb_true >if_t
     lapply ssc_in * * * * #_ #_ #_ #Hv #_ >Hv
     [ 2: lapply (Hline2 … (transitive_le … (le_maxr … H)Hsn))
       lapply fresh_var_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
     #gea2 #gca1 >gamma_distro
     >aux_read_back1 >gamma_v_to_var >gamma_var_ns 
     [ 2: cut (∀x. n ≤ x → domb_e (νx) e = false)
       [ #k lapply (Hbound1 … k) cases domb_e
         [ 2: #_ #_ @refl ]
         #HA #HB @False_ind lapply (transitive_le … (HA (refl …)) HB) @le_Sn_n
       ] #Hdom22 @Hdom22 cut (l ≤ l + e_len_c 〈b, e〉) [ // ]
       #HA @(transitive_le … (transitive_le … (le_S … Hnm) (le_maxl … (le_maxl … H'))))
       @HA ] whd in match (read_back_v ?); >push_lemma whd in match (match ? in Substitution with [_⇒?]);
       >atomic_subst >gamma_v_ns
       [ 2: * #k #Hk @(Hvar_hole2 … (transitive_le … (le_maxr … H)Hsn))
         [ 2: @Hbound1 @Hk ] @(transitive_le … (le_maxr … H) (Hldom1 … Hk)) ]
       whd in match (hole_subst ? ?); whd in match (rv_context ?); @or_intror %
       [ lapply (H1' 〈B, E〉 (crc (pi1 Byte ?
      (gamma_b b (beta_e e l)
       (alpha_to_gamma_aux2 b e l
        (gamma_lemma_aux1 〈b,e〉 (crc (AppValue (var νm) vv) (envc Epsilon νm)) l
         (fv_plug_aux1 m vv b e l H'))))) (envc X y)) l (le_maxl … H) ?)
         [ lapply H' <fresh_var_push
           change with (max ? ?) in match (fresh_var_e ?);
           change with (max ? ?) in match (fresh_var_s ?); #HH @to_max
           [ @(le_maxr … (le_maxr … (le_maxr … HH)))
           | @(le_maxl … (le_maxr … HH))
           ]
         | whd in match (plug_c ? ?);
           whd in match (plug_e ? ?);
           >alpha_be_to_gamma #HH
           lapply (HH ?)
           [ @eq_f2 [ // | @Hb ] ]
           whd in match (match ? in CrumbleContext with [_⇒?]); //
         ]
       | >stronger_aux_read_back3
         [ @tc_value_rb lapply fvb_tcterm * #Ht #_ @Ht -Ht lapply Hb' cases y #ny
           -Hb' #Hb' lapply (Hb' ny) >domb_concat_distr
           whd in match (domb_e ? ?); >veqb_true >if_t whd in match (orb ? ?);
           #HH lapply (HH (refl …)) -HH * #Hny #_
           cut (fvb_v (νny) vv= false)
           [ <(Hfvv2 … (transitive_le … (le_maxr … H) Hsn))
             cut (inb_tv (νny) v2 = false) 
             [ cut (fresh_var_tv v2 ≤ ny)
               [ @(transitive_le … (transitive_le … (le_S … (transitive_le … (transitive_le … (le_maxr … H) Hsn) Hnm)) (le_maxl … (le_maxl … H'))) Hny)
               ]
               lapply fresh_var_to_in * #_ #Hv @Hv
             ]
             @bool_impl_inv2 lapply (fv_to_in_term) * #_ #Hv @Hv
           ]
           lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @bool_impl_inv2 @Hv
         ]
         #k >dom_push whd in match (domb_e ? ?);
         cut (veqb k (ν(l+e_len_c 〈b, e〉)) = true ∨ veqb k (ν(l+e_len_c 〈b, e〉)) = false ) // * #Hk >Hk
         [ >if_t elim (veqb_true_to_eq k (ν(l+e_len_c 〈b, e〉))) #Heq #_ lapply (Heq Hk)
           -Heq #Hk destruct #_
           cut (fvb_v (ν(l+e_len_c 〈b, e〉)) vv= false)
           [ <(Hfvv2 … (transitive_le … (le_maxr … H) Hsn))
             cut (inb_tv (ν(l+e_len_c 〈b, e〉)) v2 = false)
             [ cut (fresh_var_tv v2 ≤ (l+e_len_c 〈b, e〉))
               [ lapply (transitive_le … (le_S … (transitive_le … (transitive_le … (le_maxr … H) Hsn) Hnm)) (le_maxl … (le_maxl … H')))
                 cut (l ≤l+ e_len_c 〈b,e〉) [ // ] #HHH #HH
                 @(transitive_le … HH HHH)
               ]
               lapply (fresh_var_to_in) * #_ #Hv @Hv ]
               @bool_impl_inv2 lapply (fv_to_in_term) * #_ #Hv @Hv 
           ]
           lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @bool_impl_inv2 @Hv
         | >if_f cases k #ny #HdomX lapply (Hb' ny) >domb_concat_distr
           whd in match (domb_e ? ?); >HdomX >if_monotone whd in match (orb ? ?);
           #HH lapply (HH (refl …)) -HH * #Hny #_
           cut (fvb_v (νny) vv= false)
           [ <(Hfvv2 … (transitive_le … (le_maxr … H) Hsn))
             cut (inb_tv (νny) v2 = false) 
             [ cut (fresh_var_tv v2 ≤ ny)
               [ @(transitive_le … (transitive_le … (le_S … (transitive_le … (transitive_le … (le_maxr … H) Hsn) Hnm)) (le_maxl … (le_maxl … H'))) Hny)
               ]
               lapply fresh_var_to_in * #_ #Hv @Hv
             ]
             @bool_impl_inv2 lapply (fv_to_in_term) * #_ #Hv @Hv
           ]
           lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @bool_impl_inv2 @Hv
         ]
       ]
     ]
 | #u1 #u2 normalize #H1 #H2 #s
   lapply (H2 s)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hbound (appl u1 u2) s)
    lapply (Hldom (appl u1 u2) s)
    lapply (Hmono1 (appl u1 u2) s)
    lapply (Hline1 (appl u1 u2) s)
    lapply (term_hole (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hbound (val_to_term v1) n)
      lapply (Hldom (val_to_term v1) n) normalize
      lapply (Hmono2 v1 n)
      lapply (Hline2 v1 n)
      lapply (H411v v1 n)
      lapply (value_hole (v1) n)
      cases (overline v1 n) #vv #m
      normalize
      change with (fresh_var_tv ?)
        in match (pi1 ? ? (fresh_var_tv_Sig ?));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (max ? ?)
        in match (if ? then fresh_var_t ? else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e ? else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?); #Hvar_hole1 #Hfvv1
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1 #Hterm_hole2
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2 * #B #E * [ normalize // ] #bb * #ee #y #l
      #Hm >concat_epsilon_e
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if ? then (S m) else ?); #H'
      whd in match (plug_c ? ?);
      whd in match (plug_e ? ?);
      whd in match (match ? in CrumbleContext with [_⇒?]);
      <alpha_c_to_alpha #Heq
      cut (pi1 … (alpha_c 〈AppValue vv (var νm),push e1 [νm←b1]〉 l H') =
      plug_c (crc bb (envc ee y)) 〈B,E〉) [ >Heq // ] -Heq #Heq
      cut (〈AppValue vv (var νm),push e1 [νm←b1]〉 =
       plug_c (crc (AppValue vv (var νm)) (envc Epsilon (νm))) 〈b1, e1〉)
      [ normalize >concat_to_push @refl ] #Heq'
      cut (pi1 … (alpha_c (CCrumble (AppValue vv (var νm)) (push e1 [νm←b1])) l H') =
           pi1 … (alpha_c (plug_c (crc (AppValue vv (var νm)) (envc Epsilon νm)) (CCrumble b1 e1)) l ?))
           [ @(fv_plug_aux2 … H')
           | cut (∀J, K.  (pi1 … (alpha_c 〈AppValue vv (var νm),push e1 [νm←b1]〉 l J))
                        =(pi1 … (alpha_c (plug_c (crc (AppValue vv (var νm)) (envc Epsilon νm)) 〈b1,e1〉) l K)))
                        [ 2: #UU @UU ] >Heq' // ]
      >Heq >gamma_lemma -Heq -Heq'
      whd in match (alpha_cc);
      whd in match (gamma_cc ? ? ?);
      whd in match (gamma_ec ? ? ?);
      #Heq lapply (plug_decomposition2 … Heq) * #Hbb *
      [ *
        [ * * * >alpha_be_to_gamma
          whd in match (pi1c ?); whd in match (pi1c ?);
          whd in match (pi2c ?); whd in match (pi2c ?);
          #Ha #Hb #Hc #Hd destruct
          whd in match (sse Epsilon ? ? ?); >gamma_epsilon
          whd in match (aux_read_back ? Epsilon);
          whd in match (beta ? ?);
          whd in match (ssb ? ? ? ?);
          whd in match (ssv (var νm) ? ? ?);
          generalize in match (gamma_cc_aux1 ? ? ? ?);
          generalize in match (gamma_ec_aux2 ? ? ? ?);
          generalize in match (alpha_lemma4 ? ? ? ?);
          >veqb_true >if_t #al4 #gea2 #gca1
          whd in match (gamma_b ? ? ?); >gamma_distro
          whd in match (read_back_b ?); >gamma_v_to_var
          whd in match (read_back_v (var ?));
          whd in match (hole_subst ? ?);
          whd in match (hole_subst (val_to_term ?) ?); >veqb_true >if_t
          whd in match (rv_context ?); @or_introl % // >gamma_v_ns
          [ 2: * #k #Hk lapply ssc_in * * * * #_ #_ #_ #Hv #_ >Hv
             [ @(Hvar_hole1 …  (transitive_le … (le_maxl … Hm) Hsn) (transitive_le … (le_maxl … Hm) (Hldom2 … Hk)) (Hbound2 … Hk)) ]
               lapply (Hline1 (transitive_le … (le_maxl … Hm) Hsn)) -Hv
               lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
          lapply ssc_in * * * * #_ #_ #_ #Hv #_ >Hv
             [ 2: lapply (Hline1 (transitive_le … (le_maxl … Hm) Hsn)) -Hv
               lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
          lapply fvb_tcterm * #Ht #_ @Ht -Ht
          >gamma_var_ns
           [ 2: cut ((domb_e (ν(l+e_len_c 〈b1,e1〉)) e1=true) ∨ (domb_e (ν(l+e_len_c 〈b1,e1〉)) e1=false)) // * #Hd //
             @False_ind lapply (Hbound2 … Hd) #HH 
             lapply (transitive_le … (le_S … (transitive_le … HH Hnm)) (le_maxr … (le_maxl … H')))
             -HH #HH cut (l ≤ (l + e_len_c 〈b1, e1〉)) [ // ] #HHH
             lapply (transitive_le … HH HHH) @le_Sn_n ]
          cut (fvb_v (ν(l+e_len_c 〈b1,e1〉)) vv=false)
            [ cut (inb_v (ν(l+e_len_c 〈b1,e1〉)) vv=false)
              [ cut (fresh_var_v vv ≤ l+e_len_c 〈b1, e1〉)
                [ lapply ((le_maxl … (le_maxl … H'))) #HH
                  cut (l ≤ (l + e_len_c 〈b1, e1〉)) [ // ] #HHH
                  @(transitive_le … HH HHH) ]
                lapply fresh_var_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
              @bool_impl_inv2 lapply (fv_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
            @bool_impl_inv2 lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @Hv
         ]
        | * #X whd in match (sse ? ? ? ?); >gamma_epsilon * #abs @False_ind
          lapply abs -abs cases X normalize
          [ #abs destruct
          | #XX #SXX #abs normalize destruct
          ]
        ]
        * #X whd in match (sse ? ? ? ?); >gamma_epsilon >concat_to_push
        >alpha_be_to_gamma
        whd in match (pi1c ?); whd in match (pi1c ?);
        whd in match (pi2c ?); whd in match (pi2c ?);
        whd in match (beta ? ?); whd in match (e_len_c ?);
        >gamma_var_ns
        [ 2: cut ((domb_e (ν(l+e_len e1)) e1=true) ∨ (domb_e (ν(l+e_len e1)) e1=false)) // * #Hd //
           @False_ind lapply (Hbound2 … Hd) #HH 
             lapply (transitive_le … (le_S … (transitive_le … HH Hnm)) (le_maxr … (le_maxl … H')))
             -HH #HH cut (l ≤ (l + e_len_c 〈b1, e1〉)) [ // ] #HHH
             lapply (transitive_le … HH HHH) @le_Sn_n ] *
        #Ha #Hb destruct whd in match (sse ? ? ? ?);
        whd in match (ssb ? ? ? ?); 
        whd in match (beta ? ?); whd in match (e_len_c ?);
        whd in match (ssv (var ?) ? ? ?);
        generalize in match (gamma_cc_aux1 ? ? ? ?);
        generalize in match (alpha_lemma4 ? ? ? ?); >veqb_true >if_t
        #al4 #gca1 >gamma_distro >aux_read_back1
        >gamma_v_to_var >gamma_var_ns
        [ 2: cut ((domb_e (ν(l+e_len e1)) e1=true) ∨ (domb_e (ν(l+e_len e1)) e1=false)) // * #Hd //
             @False_ind lapply (Hbound2 … Hd) #HH 
             lapply (transitive_le … (le_S … (transitive_le … HH Hnm)) (le_maxr … (le_maxl … H')))
             -HH #HH cut (l ≤ (l + e_len_c 〈b1, e1〉)) [ // ] #HHH
             lapply (transitive_le … HH HHH) @le_Sn_n ]
        whd in match (read_back_v (var ?));
        >(push_lemma (val_to_term (pvar ν(l+e_len e1))))
        whd in match (match ? in Substitution with [_⇒?]); >atomic_subst
        lapply ssc_in * * * * #_ #_ #_ #Hv #_
        generalize in match (gamma_btovl ? ? ? ?); >Hv
        [ 2: lapply (Hline1 (transitive_le … (le_maxl … Hm) Hsn))
          lapply fresh_var_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
        >gamma_v_ns
        [ 2: * #k #Hk @(Hvar_hole1 …  (transitive_le … (le_maxl … Hm) Hsn) (transitive_le … (le_maxl … Hm) (Hldom2 … Hk)) (Hbound2 … Hk))
        | 3: elim gca1 #Ha #Hb % // #k -Hb lapply (Ha k)
          lapply ssc_in * * * * #_ #_ #_ #Hv #_ >Hv
          [ 2: lapply (Hline1 (transitive_le … (le_maxl … Hm) Hsn))
            lapply fresh_var_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
          #HH #HHH lapply (HH HHH) normalize cases inb_v // >if_t #H @H ]
        >push_lemma
        whd in match (match ? in Substitution with [_⇒?]); >no_subst5
        [ 2: cut (fvb_v (ν(l+e_len e1)) vv=false)
          [ cut (inb_v (ν(l+e_len e1)) vv=false)
            [ cut (l ≤ l + e_len e1) [ // ] #HH lapply (transitive_le … (le_maxl … (le_maxl … H')) HH)
              lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
            @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
          @bool_impl_inv2 lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @Hv ]
        #Huseless >stronger_aux_read_back3
        [ 2: * #k #Hk cut (fvb_v (νk) vv=false)
          [ cut (inb_v (νk) vv=false)
            [ lapply (alphae_domain_bound e1 l (alpha_to_gamma_aux11 b1 e1 l
     (gamma_lemma_aux1 〈b1,e1〉 (crc (AppValue vv (var νm)) (envc Epsilon νm)) l
      (fv_plug_aux2 m vv b1 e1 l H'))) k) >Hb >domb_concat_distr
      whd in match (domb_e ? ?); >Hk >if_monotone whd in match (orb true ?);
      #HH elim (HH (refl …)) -HH #HH #_ lapply (transitive_le … (le_maxl … (le_maxl … H')) HH)
      lapply fresh_var_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
          @bool_impl_inv2 lapply (fv_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @Hv ]
      whd in match (hole_subst ? ?); whd in match (rv_context ?); @or_introl %
      [ lapply fvb_tcterm * #Ht #_ @Ht lapply (alphae_domain_bound e1 l (alpha_to_gamma_aux11 b1 e1 l
     (gamma_lemma_aux1 〈b1,e1〉 (crc (AppValue vv (var νm)) (envc Epsilon νm)) l
      (fv_plug_aux2 m vv b1 e1 l H')))) >Hb -Ht cases y #ny #HH lapply (HH ny) -HH
      >domb_concat_distr whd in match (domb_e ? ?); >veqb_true >if_t
      whd in match (orb true ?); #HH elim (HH (refl …)) -HH #HH #_
      cut (fvb_v (νny) vv=false)
      [ cut (inb_v (νny) vv=false)
        [ lapply (transitive_le … (le_maxl … (le_maxl … H')) HH)
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hv #_ @Hv ]
        @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #_ #Hv #_ @Hv ]
      @bool_impl_inv2 lapply fv_lemma * * * * #_ #_ #_ #Hv #_ @Hv ]
      lapply (H2 〈B, E〉 (crc (pi1 … (gamma_b b1 (beta_e e1 l)
       (alpha_to_gamma_aux2 b1 e1 l
        (gamma_lemma_aux1 〈b1,e1〉 (crc (AppValue vv (var νm)) (envc Epsilon νm))
         l (fv_plug_aux2 m vv b1 e1 l H'))))) (envc X y)) l (le_maxr … Hm) ? ?)
      [ >alpha_be_to_gamma whd in match (plug_c ? ?); @eq_f2
        [ // | whd in match (plug_e ? ?); // ]
      | skip ]
      whd in match (match ? in CrumbleContext with [_⇒?]); //
    | #r1 #r2 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hbound (appl r1 r2) n)
      lapply (Hldom (appl r1 r2) n)
      lapply (Hmono1 (appl r1 r2) n)
      lapply (Hline1 (appl r1 r2) n)
      lapply (term_hole (appl r1 r2) n)
      change with (underline_pifTerm (appl r1 r2) n)
        in match ( match r2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl r1 r2) n ) * #b #e #m #Hterm_hole1
      normalize
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r2));
      change with (max ? ?)
        in match (if ? then fresh_var_t r2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_t u2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e1 else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?);
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1'
      #Hterm_hole2 #Hline2 #Hsn #Hldom2 #Hbound2
      #H2' * #B #E * [ // ] #bb * #ee #y #l #Hm
      whd in match (plug_c ? ?);
      whd in match (plug_e ? ?);
      whd in match (match ?  in CrumbleContext with [_⇒?]);
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max (S (S ?)) (S ?)) in match (if ? then S m else ?);
      #H' >(alpha_be_to_gamma (AppValue (var ν(S m)) (var νm))
      (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H') #Heq destruct
      >gamma_distro
      (*****************************************************)

      






      whd in match (hole_subst ? ?);
      check gammae_concat_irrelevance
      >aux_read_back1 whd in match (hole_subst ? ?);
      >alpha_e_concat in e0; #e0
      lapply (concat_decomposition1 … e0) * 
      [ * #X * #Ha #Hb >gamma_e_irrelevance in Ha;
        [ 2: >fresh_var_concat in H'; #H' @(le_maxr … (le_maxr … H'))
          | 3: * #k #Hk >inb_alphae_false1 [ // ]
            [ lapply Hk >dom_push >inb_push
              normalize cut (neqb k m = true ∨ neqb k m = false) // * #Hkm >Hkm
              [ #_ elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq
                #Heqq destruct >neqb_false >if_f
                cut (inb_b (νm) b = false)
                [ lapply (le_maxl … (Hline1 … (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb ]
                cut (inb_e (νm) e = false)
                [ lapply (le_maxr … (Hline1 … (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #_ #Hb #_ #_ @Hb ]
                  #Ha >Ha #Hb >Hb //
              ]
              >if_f -Hk #Hk
              cut (inb_b (νk) b = false)
                [ lapply (Hterm_hole1 k ? ? ?)
                  [ @Hbound2  @Hk
                  | @(transitive_le … (le_maxl … Hm) (Hldom2 … Hk))
                  | @(transitive_le … (le_maxl … Hm) Hsn)
                  | #HH elim (orb_false … HH) //
                  ]
                 ]
              cut (inb_e (νk) e = false)
                [ lapply (Hterm_hole1 k ? ? ?)
                  [ @Hbound2  @Hk
                  | @(transitive_le … (le_maxl … Hm) (Hldom2 … Hk))
                  | @(transitive_le … (le_maxl … Hm) Hsn)
                  | #HH elim (orb_false … HH) //
                  ]
                 ]
                  #Ha >Ha #Hb >Hb
                  cut (neqb k (S m)= true ∨ neqb k (S m)= false) // * #Hmsk
                  >Hmsk // elim (neqb_iff_eq k (S m)) #Heqq lapply (Heqq … Hmsk)
                  -Heqq #Heqq  #_ -Heq -H1 -H2 -e0 -Ha -Hb destruct
                  @False_ind
                  lapply (le_S … (transitive_le … (Hbound2 … Hk) Hnm)) @le_Sn_n
            ] >e_len_push <plus_n_Sm lapply Hk >dom_push normalize
            cut (neqb k m = true ∨ neqb k m = false) // * #Hkm >Hkm
            [ #_ elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq
              #Heqq destruct cut (S m ≤ l + e_len e1)
                [ lapply (le_maxr … (le_maxl … H')) #HH @le_plus_a_r @HH ]
               #HH @(le_S … HH) ]
            >if_f #Hdomb lapply (transitive_le … (le_S … (transitive_le … (Hbound2 … Hdomb) Hnm)) (le_maxr … (le_maxl … H')))
            #HH lapply (le_plus_a_r  (e_len e1)l  l (le_n …)) #HHH
            @(le_S … (transitive_le … HH HHH)) ] >alpha_push #Ha
            lapply (push_eq_concat_cons … Ha) *
            [ * * #Haa #Hbb #Hcc destruct >gamma_v_to_var >gamma_var_simplification2
              [ 2: lapply (le_maxr … H') >fresh_var_concat >fresh_var_concat
        -H' #H' @to_max
        [ @(le_maxr … H') | @(le_maxl … H') ] 
      | 3: >dom_push whd in match (domb_e ? ?); >veqb_simm whd in match (veqb ? ?); 
        >neqb_false >if_f cut (domb_e (ν (S m)) e1 = true ∨ domb_e (ν (S m)) e1 = false) // * //
        #HH @False_ind lapply (le_S … (transitive_le … (Hbound2 … HH) Hnm)) @le_Sn_n
      | 4: cut (domb_e (ν (S m)) e = true ∨ domb_e (ν (S m)) e = false) // * //
        #HH @False_ind lapply (le_S … (Hbound1 … HH)) @le_Sn_n ]
              whd in match (read_back_v ?); whd in match (aux_read_back ? ?);
              whd in match (hole_subst ? ?); >veqb_true >if_t
              whd in match (rv_context ?); @or_intror % //
              >gamma_v_to_var >gamma_var_simplification1
              [ 2: @(le_maxr … H')
      | 3: >dom_push whd in match (domb_e ? ?); whd in match (veqb ? ?);
        >neqb_false >if_f cut (domb_e (νm) e = true ∨ domb_e (νm) e = false) // * //
        #HH @False_ind lapply (Hbound1 … HH) @le_Sn_n
      | 4: cut (domb_e (νm) e1 = true ∨ domb_e (νm) e1 = false) // * //
        #HH @False_ind lapply (transitive_le … (Hbound2 … HH) Hnm) @le_Sn_n ]
              normalize >e_len_push <plus_n_Sm whd in match (?+?);
              cut (neqb (l+e_len e1) (S (l+e_len e1)+e_len e) = true ∨
                   neqb (l+e_len e1) (S (l+e_len e1)+e_len e) = false) // * #Htf
              >Htf // elim (neqb_iff_eq (l+e_len e1) (S (l+e_len e1)+e_len e))
              #Heq lapply (Heq Htf) -Heq #Heqq #_
              @False_ind lapply Heqq -H1 -H2 -Heq -e0 -e2 -Ha
                cut (l+e_len e1 < S (l+e_len e1)+e_len e)
                [ normalize // ] #HH lapply (lt_to_not_eq … HH) -HH * #HH @HH ]
              * #Y * #Haa #Hbb destruct >gamma_v_to_var >gamma_var_simplification2
              [ 2: lapply (le_maxr … H') >fresh_var_concat >fresh_var_concat
        -H' #H' @to_max
        [ @(le_maxr … H') | @(le_maxl … H') ] 
      | 3: >dom_push whd in match (domb_e ? ?); >veqb_simm whd in match (veqb ? ?); 
        >neqb_false >if_f cut (domb_e (ν (S m)) e1 = true ∨ domb_e (ν (S m)) e1 = false) // * //
        #HH @False_ind lapply (le_S … (transitive_le … (Hbound2 … HH) Hnm)) @le_Sn_n
      | 4: cut (domb_e (ν (S m)) e = true ∨ domb_e (ν (S m)) e = false) // * //
        #HH @False_ind lapply (le_S … (Hbound1 … HH)) @le_Sn_n ]
              whd in match (read_back_v ?); >push_lemma
              whd in match (match ? in Substitution with [_⇒?]);
              >atomic_subst >gamma_v_to_var >gamma_var_simplification1
              [ 2: @(le_maxr … H')
      | 3: >dom_push whd in match (domb_e ? ?); whd in match (veqb ? ?);
        >neqb_false >if_f cut (domb_e (νm) e = true ∨ domb_e (νm) e = false) // * //
        #HH @False_ind lapply (Hbound1 … HH) @le_Sn_n
      | 4: cut (domb_e (νm) e1 = true ∨ domb_e (νm) e1 = false) // * //
        #HH @False_ind lapply (transitive_le … (Hbound2 … HH) Hnm) @le_Sn_n ]
              >push_lemma >no_subst
              [ 2: -e2 -Heq -Ha -H2 -e0 >e_len_push normalize <plus_n_Sm
                cut (l+e_len e1 < S (l+e_len e1)+e_len e)
                [ normalize // ] #HH lapply (lt_to_not_eq … HH) -HH * #HH
                cut (neqb (S (l+e_len e1)+e_len e) (l+e_len e1)=true ∨ (neqb (S (l+e_len e1)+e_len e) (l+e_len e1)=false))
                // * #Htf // @False_ind @HH
                elim (neqb_iff_eq  (S (l+e_len e1)+e_len e) (l+e_len e1)) #Heq #_
                >Heq // ]
              >alpha_e_concat in e2; <(concat_switch ? ? X) #ee
              lapply (concat_same_len … ee) [ >alpha_e_len // ] * #e2 #_
              >gamma_e_irrelevance in e2;
                 [ 2: >fresh_var_concat in H'; #H' @(le_maxr … (le_maxr … H'))
          | 3: * #k #Hk >inb_alphae_false1 [ // ]
            [ lapply Hk >dom_push >inb_push
              normalize cut (neqb k m = true ∨ neqb k m = false) // * #Hkm >Hkm
              [ #_ elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq
                #Heqq destruct >neqb_false >if_f
                cut (inb_b (νm) b = false)
                [ lapply (le_maxl … (Hline1 … (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb ]
                cut (inb_e (νm) e = false)
                [ lapply (le_maxr … (Hline1 … (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #_ #Hb #_ #_ @Hb ]
                  #Ha >Ha #Hb >Hb //
              ]
              >if_f -Hk #Hk
              cut (inb_b (νk) b = false)
                [ lapply (Hterm_hole1 k ? ? ?)
                  [ @Hbound2  @Hk
                  | @(transitive_le … (le_maxl … Hm) (Hldom2 … Hk))
                  | @(transitive_le … (le_maxl … Hm) Hsn)
                  | #HH elim (orb_false … HH) //
                  ]
                 ]
              cut (inb_e (νk) e = false)
                [ lapply (Hterm_hole1 k ? ? ?)
                  [ @Hbound2  @Hk
                  | @(transitive_le … (le_maxl … Hm) (Hldom2 … Hk))
                  | @(transitive_le … (le_maxl … Hm) Hsn)
                  | #HH elim (orb_false … HH) //
                  ]
                 ]
                  #Ha >Ha #Hb >Hb
                  cut (neqb k (S m)= true ∨ neqb k (S m)= false) // * #Hmsk
                  >Hmsk // elim (neqb_iff_eq k (S m)) #Heqq lapply (Heqq … Hmsk)
                  -Heqq #Heqq  #_-Heq -H1 -H2 -e0 -Ha -Hb destruct
                  @False_ind
                  lapply (le_S … (transitive_le … (Hbound2 … Hk) Hnm)) @le_Sn_n
            ] normalize >e_len_push <plus_n_Sm lapply Hk >dom_push normalize
            cut (neqb k m = true ∨ neqb k m = false) // * #Hkm >Hkm
            [ #_ elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq
              #Heqq destruct cut (S m ≤ l + e_len e1)
                [ lapply (le_maxr … (le_maxl … H')) #HH @le_plus_a_r @HH ]
               #HH @(le_S … HH) ]
            >if_f #Hdomb lapply (transitive_le … (le_S … (transitive_le … (Hbound2 … Hdomb) Hnm)) (le_maxr … (le_maxl … H')))
            #HH lapply (le_plus_a_r  (e_len e1)l  l (le_n …)) #HHH
            @(le_S … (transitive_le … HH HHH)) ] #e2 whd in match (rv_context ?);
            @or_intror % [2:
            lapply (alphae_domain_bound (push e [ν(S m)←b]) (l+e_len (push e1 [νm←b1]))
    (alphae_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
     (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
      (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H')))
            >e2 #Hdom
             >stronger_aux_read_back3
             [ 2: * #k #Hk lapply (Hdom k) >domb_concat_distr
            whd in match (domb_e ? ?); >dom_push
            whd in match (domb_e ? ?); >Hk >if_monotone >if_monotone
            normalize in match (orb ? ?);
            -Hdom #Hdom elim (Hdom (refl … )) #HH #_
            normalize cut (neqb k (l+e_len e1)= true ∨ neqb k (l+e_len e1)= false)
            // * #Htf >Htf //
            elim (neqb_iff_eq k (l+e_len e1)) #Heqq #_ lapply (Heqq Htf) -Heqq
            #Heqq destruct @False_ind lapply HH >e_len_push <plus_n_Sm
            @le_Sn_n ] whd in match (hole_subst ? ?);
            cut (veqb (ν(l+e_len e1)) y = false)
              [ lapply Hdom  elim y #ny #Hdom lapply (Hdom ny)
            >domb_concat_distr whd in match (domb_e ? ?); >veqb_true >if_t
            whd in match (orb ? ?); -Hdom #Hdom elim (Hdom (refl …)) -Hdom #Hny #_
            normalize cut (neqb ny (l+e_len e1)= true ∨ neqb ny (l+e_len e1)= false)
            // * #Htf >Htf //
            elim (neqb_iff_eq ny (l+e_len e1)) #Heqq #_ lapply (Heqq Htf) -Heqq
            #Heqq destruct @False_ind lapply Hny >e_len_push <plus_n_Sm
            @le_Sn_n ] #HH >HH >if_f // ]
            lapply (H1' (CCrumble B X) (crc (pi1 … (gamma_b b (beta_e e (l+e_len (push e1 [νm←b1]))) ?))
     (envc Y y) ) (l+(e_len (push e1 [νm←b1]))) (transitive_le … (le_maxl … Hm) Hsn) ?)
            [ 2: @((alpha_push_aux2 e (ν(S m)) b (l+e_len (push e1 [νm←b1]))
         (alphae_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
          (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
           (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H'))))
            | cut (l ≤ l+ e_len (push e1 [νm←b1])) [ // ] #Hf
          lapply (le_maxr … H') >fresh_var_concat <fresh_var_push
          change with (max ? (max ? ?)) in match (fresh_var_e ?); #HH
          @to_max
          [ @(transitive_le … (le_maxr … (le_maxr … (le_maxl … HH))) Hf)
          | @(transitive_le … (le_maxl … (le_maxl … HH)) Hf)
          ]
          | whd in match (plug_c ? ?);
            whd in match (plug_e ? ?);
            whd in match (match ? in CrumbleContext with [_⇒?]); #HH @HH
            >alpha_be_to_gamma @eq_f2 // >alpha_push in e2; #e2
            cut (∀a,b,c,d. concat (Cons (push a b) c) d = push (concat (Cons a c) d) b)
            [ -H2 -H1 -e2 -Ha -e0 -e1 #a #b #c #d /3/]
            #Hs >Hs in e2; #e2 lapply (push_eq_inv … e2) * #HH #Hbb <HH //
            ]
      | * #X * #Ha #Hb >alpha_push in Hb; #Hb >gamma_e_irrelevance in Ha;
        [ 2: >fresh_var_concat in H'; #H' @(le_maxr … (le_maxr … H'))
          | 3: * #k #Hk >inb_alphae_false1 [ // ]
            [ lapply Hk >dom_push >inb_push
              normalize cut (neqb k m = true ∨ neqb k m = false) // * #Hkm >Hkm
              [ #_ elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq
                #Heqq destruct >neqb_false >if_f
                cut (inb_b (νm) b = false)
                [ lapply (le_maxl … (Hline1 … (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_ @Hb ]
                cut (inb_e (νm) e = false)
                [ lapply (le_maxr … (Hline1 … (transitive_le … (le_maxl … Hm) Hsn)))
                  lapply fresh_var_to_in_crumble * * * * #_ #_ #Hb #_ #_ @Hb ]
                  #Ha >Ha #Hb >Hb //
              ]
              >if_f -Hk #Hk
              cut (inb_b (νk) b = false)
                [ lapply (Hterm_hole1 k ? ? ?)
                  [ @Hbound2  @Hk
                  | @(transitive_le … (le_maxl … Hm) (Hldom2 … Hk))
                  | @(transitive_le … (le_maxl … Hm) Hsn)
                  | #HH elim (orb_false … HH) //
                  ]
                 ]
              cut (inb_e (νk) e = false)
                [ lapply (Hterm_hole1 k ? ? ?)
                  [ @Hbound2  @Hk
                  | @(transitive_le … (le_maxl … Hm) (Hldom2 … Hk))
                  | @(transitive_le … (le_maxl … Hm) Hsn)
                  | #HH elim (orb_false … HH) //
                  ]
                 ]
                  #Ha >Ha #Hb >Hb
                  cut (neqb k (S m)= true ∨ neqb k (S m)= false) // * #Hmsk
                  >Hmsk // elim (neqb_iff_eq k (S m)) #Heqq lapply (Heqq … Hmsk)
                  -Heqq #Heqq  #_ -Heq -H1 -H2 -e0 -Ha -Hb destruct
                  @False_ind
                  lapply (le_S … (transitive_le … (Hbound2 … Hk) Hnm)) @le_Sn_n
            ] >e_len_push <plus_n_Sm lapply Hk >dom_push normalize
            cut (neqb k m = true ∨ neqb k m = false) // * #Hkm >Hkm
            [ #_ elim (neqb_iff_eq … k m) #Heq #_ lapply (Heq Hkm) -Heq
              #Heqq destruct cut (S m ≤ l + e_len e1)
                [ lapply (le_maxr … (le_maxl … H')) #HH @le_plus_a_r @HH ]
               #HH @(le_S … HH) ]
            >if_f #Hdomb lapply (transitive_le … (le_S … (transitive_le … (Hbound2 … Hdomb) Hnm)) (le_maxr … (le_maxl … H')))
            #HH lapply (le_plus_a_r  (e_len e1)l  l (le_n …)) #HHH
            @(le_S … (transitive_le … HH HHH)) 
        ] #Ha elim (push_eq_concat … Hb)
        [ 2: * #Haa #Hbb destruct >concat_epsilon_e in Hb; >concat_e_epsilon in Ha;
          #Ha #_ >alpha_push in Ha; #Ha lapply (cons_push_decomposition … Ha) *
          [ * * #Haaa #Hbbb #Hccc destruct >Hbbb 
            change with (read_back_v ?) in match (aux_read_back ? Epsilon);
            change with (read_back_v ?) in match (aux_read_back ? Epsilon);
            >gamma_v_to_var  whd in match (rv_context ?); @or_intror %
          [ >gamma_var_simplification2
            [ 2: lapply (le_maxr … H') >fresh_var_concat >fresh_var_concat
        -H' #H' @to_max
        [ @(le_maxr … H') | @(le_maxl … H') ] 
      | 3: >dom_push whd in match (domb_e ? ?); >veqb_simm whd in match (veqb ? ?); 
        >neqb_false >if_f cut (domb_e (ν (S m)) e1 = true ∨ domb_e (ν (S m)) e1 = false) // * //
        #HH @False_ind lapply (le_S … (transitive_le … (Hbound2 … HH) Hnm)) @le_Sn_n
      | 4: cut (domb_e (ν (S m)) e = true ∨ domb_e (ν (S m)) e = false) // * //
        #HH @False_ind lapply (le_S … (Hbound1 … HH)) @le_Sn_n ]
        normalize >neqb_refl >if_t //
      | >gamma_v_to_var whd in match (aux_read_back ? Epsilon);
        >gamma_var_simplification1
              [ 2: @(le_maxr … H')
      | 3: >dom_push whd in match (domb_e ? ?); whd in match (veqb ? ?);
        >neqb_false >if_f cut (domb_e (νm) e = true ∨ domb_e (νm) e = false) // * //
        #HH @False_ind lapply (Hbound1 … HH) @le_Sn_n
      | 4: cut (domb_e (νm) e1 = true ∨ domb_e (νm) e1 = false) // * //
        #HH @False_ind lapply (transitive_le … (Hbound2 … HH) Hnm) @le_Sn_n ]
        -e3 -e2 -e0 -Heq -Ha -Hbbb normalize
        >e_len_push normalize <plus_n_Sm
                cut (l+e_len e1 < S (l+e_len e1)+e_len e)
                [ normalize // ] #HH lapply (lt_to_not_eq … HH) -HH * #HH
                cut (neqb (S (l+e_len e1)+e_len e) (l+e_len e1)=true ∨ (neqb (S (l+e_len e1)+e_len e) (l+e_len e1)=false))
                // * #Htf >neq_simm >Htf normalize // @False_ind @HH
                elim (neqb_iff_eq  (S (l+e_len e1)+e_len e) (l+e_len e1)) #Heq #_
                >Heq // ]
       ]
      * #Y * #Haa #Hbb  destruct whd in match (rv_context ?); @or_intror %
      [ -e0 -e2 -e3 >gamma_v_to_var >gamma_var_simplification2
      [ 2: lapply (le_maxr … H') >fresh_var_concat >fresh_var_concat
        -H' #H' @to_max
        [ @(le_maxr … H') | @(le_maxl … H') ] 
      | 3: >dom_push whd in match (domb_e ? ?); >veqb_simm whd in match (veqb ? ?); 
        >neqb_false >if_f cut (domb_e (ν (S m)) e1 = true ∨ domb_e (ν (S m)) e1 = false) // * //
        #HH @False_ind lapply (le_S … (transitive_le … (Hbound2 … HH) Hnm)) @le_Sn_n
      | 4: cut (domb_e (ν (S m)) e = true ∨ domb_e (ν (S m)) e = false) // * //
        #HH @False_ind lapply (le_S … (Hbound1 … HH)) @le_Sn_n ]
      >push_lemma whd in match (match ? in Substitution with [_⇒?]);
      >atomic_subst lapply (H1' 〈B, Epsilon〉
      (crc (pi1 … (gamma_b b (beta_e e (l+e_len (push e1 [νm←b1])))
        (alpha_push_aux2 e (ν(S m)) b (l+e_len (push e1 [νm←b1]))
         (alphae_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
          (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
           (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H'))))) (envc Y y)) (l+e_len (push e1 [νm←b1]))
           (transitive_le … (le_maxl … Hm) Hsn) ? )
      [ cut (l ≤ l+ e_len (push e1 [νm←b1])) [ // ] #Hf
          lapply (le_maxr … H') >fresh_var_concat <fresh_var_push
          change with (max ? (max ? ?)) in match (fresh_var_e ?); #HH
          @to_max
          [ @(transitive_le … (le_maxr … (le_maxr … (le_maxl … HH))) Hf)
          | @(transitive_le … (le_maxl … (le_maxl … HH)) Hf)
          ]
      ] #HH @(HH ?) whd in match (plug_c ? ?); whd in match (plug_e ? ?);
        >alpha_be_to_gamma @eq_f2 // lapply Ha
        change with (push (Cons ? ?) ?) in match (Cons (push ? ?) ?);
        #Ha lapply (push_eq_inv … Ha) * #HH #_ >HH //
      | >gamma_v_to_var >gamma_var_simplification1
        [ 2: @(le_maxr … H')
      | 3: >dom_push whd in match (domb_e ? ?); whd in match (veqb ? ?);
        >neqb_false >if_f cut (domb_e (νm) e = true ∨ domb_e (νm) e = false) // * //
        #HH @False_ind lapply (Hbound1 … HH) @le_Sn_n
      | 4: cut (domb_e (νm) e1 = true ∨ domb_e (νm) e1 = false) // * //
        #HH @False_ind lapply (transitive_le … (Hbound2 … HH) Hnm) @le_Sn_n ]
        >push_lemma >no_subst5
        [ 2: >e_len_push whd in match (read_back_v ?);
          normalize <plus_n_Sm
          cut (l+e_len e1 < S (l+e_len e1)+e_len e)
                [ normalize // ] #HH lapply (lt_to_not_eq … HH) -HH * #HH
                cut (neqb (S (l+e_len e1)+e_len e) (l+e_len e1)=true ∨ (neqb (S (l+e_len e1)+e_len e) (l+e_len e1)=false))
                // * #Htf >neq_simm >neq_simm >Htf normalize // @False_ind @HH
                elim (neqb_iff_eq  (S (l+e_len e1)+e_len e) (l+e_len e1)) #Heq #_
                >Heq // ]
        lapply Ha
        change with (push (Cons ? ?) ?) in match (Cons (push ? ?) ?);
        #Ha lapply (push_eq_inv … Ha) * #HH #_
        lapply (alphae_domain_bound e (l+e_len (push e1 [νm←b1])) (alpha_push_aux1 e (ν(S m)) b (l+e_len (push e1 [νm←b1]))
      (alphae_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
       (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
        (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H')))) <HH -HH #HH
        >stronger_aux_read_back3
        [ 2:  * #k #Hk
        lapply (HH k) whd in match (domb_e ? ?); >Hk >if_monotone -HH #HH
        lapply (HH … (refl …)) * -HH #HH #_ lapply HH normalize
        cut (neqb k (l+e_len e1) = true ∨ neqb k (l+e_len e1) = false) // * #Hkn >Hkn // 
        elim (neqb_iff_eq k (l+e_len e1)) #Heqq lapply (Heqq Hkn) -Heqq #Heqq #_
        >e_len_push <plus_n_Sm #ABS @False_ind lapply ABS >Heqq @le_Sn_n ]
        lapply HH cases y #ny -HH #HH lapply (HH ny) whd in match (domb_e ? ?);
        >veqb_true >if_t -HH #HH lapply (HH (refl …)) * -HH #HH #_ lapply HH normalize
        cut (neqb (l+e_len e1) ny = true ∨ neqb (l+e_len e1) ny = false) // * #Hkn >Hkn // 
        elim (neqb_iff_eq (l+e_len e1) ny) #Heqq lapply (Heqq Hkn) -Heqq #Heqq #_
        >e_len_push <plus_n_Sm #ABS @False_ind lapply ABS >Heqq @le_Sn_n ]
     | * #Y * #Haa #Hbb >Haa in Ha; #Ha lapply (cons_concat … Ha) *
       [ * #Haaa #Hbbb destruct @False_ind -Heq -Ha -Hb -Hbb -H2 -e0 (lapply Hbbb) -e2 -Haaa
         cases Y [ normalize #abs destruct | #rr #ss whd in match (push ? ?);
           generalize in match (push ? ?); #C #abs destruct ]
     | * #Z * #Haaa #Hbbb destruct whd in match (rv_context ?); @or_introl
       >alpha_e_concat in e2; >env_lemma5 >concat_switch #e2
       lapply (concat_same_len2 … e2) [ >gamma_len >alpha_e_len // ]
       * #_ >alpha_push <(env_lemma5 E Z) #HH
       >gamma_v_to_var >gamma_var_simplification2
      [ 2: lapply (le_maxr … H') >fresh_var_concat >fresh_var_concat
        -H' #H' @to_max
        [ @(le_maxr … H') | @(le_maxl … H') ] 
      | 3: >dom_push whd in match (domb_e ? ?); >veqb_simm whd in match (veqb ? ?); 
        >neqb_false >if_f cut (domb_e (ν (S m)) e1 = true ∨ domb_e (ν (S m)) e1 = false) // * //
        #HH @False_ind lapply (le_S … (transitive_le … (Hbound2 … HH) Hnm)) @le_Sn_n
      | 4: cut (domb_e (ν (S m)) e = true ∨ domb_e (ν (S m)) e = false) // * //
        #HH @False_ind lapply (le_S … (Hbound1 … HH)) @le_Sn_n ]
         lapply (push_eq_concat_cons … HH) *
       [ * * #Ha1 #Hb2 #Hc3 destruct >concat_e_epsilon %
         [ 2: >gamma_v_to_var >gamma_var_simplification1
      [ 2: @(le_maxr … H')
      | 3: >dom_push whd in match (domb_e ? ?); whd in match (veqb ? ?);
        >neqb_false >if_f cut (domb_e (νm) e = true ∨ domb_e (νm) e = false) // * //
        #HH @False_ind lapply (Hbound1 … HH) @le_Sn_n
      | 4: cut (domb_e (νm) e1 = true ∨ domb_e (νm) e1 = false) // * //
        #HH @False_ind lapply (transitive_le … (Hbound2 … HH) Hnm) @le_Sn_n ]
        whd in match (read_back_v (var ν(l+e_len e1)));
        >stronger_aux_read_back3 [ normalize >neqb_refl >if_t // ]
        * #k #Hk lapply (alphae_domain_bound (push e [ν(S m)←b]) (l+e_len (push e1 [νm←b1]))
     (alphae_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
      (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
       (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H')) k Hk)
       * #Hk #_ normalize
          cut (l+e_len e1 < k)
                [ normalize // ] #HH lapply (lt_to_not_eq … HH) -HH * #HH
                cut (neqb k (l+e_len e1)=true ∨ (neqb k (l+e_len e1)=false))
                // * #Htf >Htf normalize // @False_ind @HH
                elim (neqb_iff_eq  k (l+e_len e1)) #Heq #_
                >Heq // ]
       >alpha_push whd in match (read_back_v (var ν(l+e_len (push e1 [νm←b1])+e_len e)));
       >push_lemma whd in match (match ? in Substitution with [_⇒?]); >atomic_subst
       lapply fvb_tcterm * #Ht #_ @Ht
       change with (read_back 〈?, ?〉)
         in match (aux_read_back ? ?);
       <alpha_be_to_gamma_pre
       [ 2: -e3 -e2 -e0 -Heq -Ha -Hb -Hbb -Hbbb -HH -H2 -H1 -H2'
         @le_plus_a_r @to_max >fresh_var_concat in H'; <fresh_var_push;
         #h' [ @(le_maxr … (le_maxr … (le_maxl … (le_maxr … h'))))
             | @(le_maxl … (le_maxl … (le_maxr … h')))
             ]
           ]
       generalize in match (le_plus_a_r ? ? ? ?); #T
       cut  (fvb (ν(l+e_len e1)) (pi1  …
    (alpha b e (l+e_len (push e1 [νm←b1])) T))= false)
       [ >alpha_fv_cons
         cut (inb (ν(l+e_len e1)) 〈b,e〉=false)
         [ cut (fresh_var 〈b,e〉 ≤ l+e_len e1)
           [ -e3 -e2 -e0 -Heq -Ha -Hb -Hbb -Hbbb -HH -H2 -H1 -H2'
             @le_plus_a_r @to_max >fresh_var_concat in H'; <fresh_var_push;
             #h' [ @(le_maxr … (le_maxr … (le_maxl … (le_maxr … h'))))
                 | @(le_maxl … (le_maxl … (le_maxr … h')))
                 ]
           ]
         lapply fresh_var_to_in_crumble * * * * #Hc #_ #_ #_ #_ @Hc ]
       lapply fv_to_in_crumble * * * * #Hc #_ #_ #_ #_ @bool_impl_inv2 @Hc
       ]
     @bool_impl_inv2 lapply fv_lemma * * * * #Hc #_ #_ #_ #_ @Hc ]
   * #W * #HW1 #HW2 >HW1 %
   [ >ultra_concat_lemma
     [ 3: cut (domb_e (ν(l+e_len (push e1 [νm←b1])+e_len e)) (concat (Cons W [y←B]) E) = false)
       [ <HW2 lapply (alphae_domain_bound e1 l
    (alpha_push_aux1 e1 (νm) b1 l
     (alpha_e_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
      (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
       (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H'))) (l+e_len (push e1 [νm←b1])+e_len e))
       cases (domb_e ? ?) // #HH @False_ind elim (HH (refl  …)) -HH #_
       >e_len_push <plus_n_Sm lapply (le_plus_a_r (e_len e) (l+e_len e1) (l+e_len e1) (le_n …))
       #HH #HHH lapply (transitive_le … HHH HH) @le_Sn_n ]
       >domb_concat_distr #HH lapply (orb_false … HH) * -HH #HH #_
       >dom_push lapply (orb_false … HH) -HH * #_ #HH whd in match (domb_e ? ?);
       >HH >if_then_true_else_false normalize
       cut (l+e_len e1 < (l+e_len (push e1 [νm←b1])+e_len e))
       [ normalize // ] #HH lapply (lt_to_not_eq … HH) -HH * #HH
       cut (neqb (l+e_len e1) (l+e_len (push e1 [νm←b1])+e_len e)=true ∨ (neqb (l+e_len e1) (l+e_len (push e1 [νm←b1])+e_len e)=false))
       // * #Htf >Htf normalize // @False_ind @HH
       elim (neqb_iff_eq  (l+e_len e1) (l+e_len (push e1 [νm←b1])+e_len e)) #Heq #_
       >Heq // ]
     [ 2: * #k #Hk cases alpha_e #dd #hh cut (inb_e (νk) dd = false)
       [ @hh whd in match (veqb ? ?);
         cut (neqb k (l+e_len e1) = true ∨ neqb k (l+e_len e1) = false) // * #Hkl
         [ elim (neqb_iff_eq k (l+e_len e1)) #Heqq #_ lapply (Heqq Hkl)
           -Heqq #Heqq destruct %
            [ >fresh_var_concat in H'; #H' @le_plus_a_r @(le_maxl … (le_maxr … H'))
            | >e_len_push <plus_n_Sm @le_n
            ]
         | lapply Hk >dom_push whd in match (domb_e ? ?);
           whd in match (veqb ? ?); >Hkl >if_f -Hk #Hk
           lapply (alphae_domain_bound e1 l
    (alpha_push_aux1 e1 (νm) b1 l
     (alpha_e_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
      (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
       (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H'))) k)
       >HW2 >domb_concat_distr whd in match (domb_e ? ?); >Hk
       >if_monotone
       whd in match (orb true ?);  #HH
       elim (HH (refl  …)) #HH1 #HH2 %
       [ 2: >e_len_push <plus_n_Sm @(le_S_S … HH2)
       | >fresh_var_concat in H'; #H'  @ (transitive_le … (le_maxl … (le_maxr … H')) HH1)
       ]
         ]
       ] @bool_impl_inv2 lapply fv_to_in_crumble * * * * #_ #_ #He #_ #_ @He
     ]
    >alpha_push >push_lemma >atomic_subst
    lapply fvb_tcterm * #Ht #_ @Ht
       change with (read_back 〈?, ?〉)
         in match (aux_read_back ? ?);
       <alpha_be_to_gamma_pre
       [ 2: -e2 -e0 -Heq -Ha -Hb -Hbb -Hbbb -HH -H2 -H1 -H2'
         @le_plus_a_r @to_max >fresh_var_concat in H'; <fresh_var_push;
         #h' [ @(le_maxr … (le_maxr … (le_maxl … (le_maxr … h'))))
             | @(le_maxl … (le_maxl … (le_maxr … h')))
             ]
           ]
       generalize in match (le_plus_a_r ? ? ? ?); #T
       cut  (fvb (y) (pi1  …
    (alpha b e (l+e_len (push e1 [νm←b1])) T))= false)
       [ >alpha_fv_cons
         cut (inb (y) 〈b,e〉=false)
         [ lapply HW2 cases y #ny -HW2 #Hw2' cut (fresh_var 〈b,e〉 ≤ ny)
           [ -e2 -e0 -Heq -Ha -Hb -Hbb -Hbbb -HH -H2 -H1 -H2'
             lapply (alphae_domain_bound e1 l
    (alpha_push_aux1 e1 (νm) b1 l
     (alpha_e_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
      (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
       (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H'))) ny) >Hw2'
       >domb_concat_distr normalize >neqb_refl >if_t #HH
       elim (HH (refl …)) -HH #HH #_ >fresh_var_concat in H';  <fresh_var_push;
       #h'  @to_max
       [  @(transitive_le … (le_maxr … (le_maxr … (le_maxl … (le_maxr … h')))) HH)
       |  @(transitive_le … (le_maxl … (le_maxl … (le_maxr … h'))) HH)
       ] ]
        lapply fresh_var_to_in_crumble * * * * #Hc #_ #_ #_ #_ @Hc ]
      @bool_impl_inv2 lapply fv_to_in_crumble * * * * #Hc #_ #_ #_ #_ @Hc ]
      lapply fv_lemma * * * * #Hc #_ #_ #_ #_ @bool_impl_inv2 @Hc ]
    >gamma_v_to_var >gamma_var_simplification1
    [ 2: @(le_maxr … H')
      | 3: >dom_push whd in match (domb_e ? ?); whd in match (veqb ? ?);
        >neqb_false >if_f cut (domb_e (νm) e = true ∨ domb_e (νm) e = false) // * //
        #HH @False_ind lapply (Hbound1 … HH) @le_Sn_n
      | 4: cut (domb_e (νm) e1 = true ∨ domb_e (νm) e1 = false) // * //
        #HH @False_ind lapply (transitive_le … (Hbound2 … HH) Hnm) @le_Sn_n ]
     whd in match (read_back_v ?);
    >iper_concat_lemma
    [ 2: lapply (alphae_domain_bound  (push e [ν(S m)←b]) (l+e_len (push e1 [νm←b1]))
    (alphae_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
     (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
      (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H')) (l+e_len e1))
      cases domb_e // #HH elim (HH (refl …)) -HH #HH @False_ind
      lapply HH >e_len_push <plus_n_Sm @le_Sn_n ]
    >push_lemma >atomic_subst
    @ (H2' (CCrumble B E) (crc (pi1 … (gamma_b b1 (beta_e e1 l)
       (alpha_push_aux2 e1 (νm) b1 l
        (alpha_e_concat_aux2 (push e1 [νm←b1]) (push e [ν(S m)←b]) l
         (alpha_to_gamma_aux11 (AppValue (var ν(S m)) (var νm))
          (concat (push e [ν(S m)←b]) (push e1 [νm←b1])) l H'))))) (envc W y))
          l (le_maxr … Hm))
    [ >fresh_var_concat in H'; <fresh_var_push <fresh_var_push #H'
      @to_max [ @(le_maxr … (le_maxr … (le_maxr … (le_maxr … H')))) |
      @(le_maxl … (le_maxr … (le_maxr … H'))) ] ] 
      whd in match (plug_c ?);
      whd in match (plug_e ? ?);
      >alpha_be_to_gamma @eq_f2 //
      whd in match (plug_e (envc W y) ?); <HW2 //
    ]
  ]
] qed.

(*
lemma dom_var_occ: 
 (∀t, s, x.
  fresh_var_t t ≤ s →
   s ≤ x →
    x < snd … (underline_pifTerm t s) → 
     free_occ (νx) (fst … (underline_pifTerm t s)) ≤ 1) ∧
 (∀v, s, x.
  fresh_var_tv v ≤ s →
   s ≤ x →
    x < snd … (overline v s) → 
     free_occ_val (νx) (fst … (overline v s)) = 0).
  
@pifValueTerm_ind
[ #v #HI #s #x #H whd in match (underline_pifTerm ??); #H1 #H2
 lapply (HI s x) lapply H2 cases overline #vv #n normalize #H2 -HI #HI
 cut (∀n. n+0=n) [ cases n // ] #Hn >Hn -Hn  >HI //
| 3: * #y #s #x #H whd in match (overline ? ?); normalize
  normalize in H; #H1 #H2 cut (neqb x y = false) [ 2: #HH >HH // ]
  cut (neqb x y = true ∨ neqb x y = false) // * #Hxy >Hxy //
  @False_ind elim (neqb_iff_eq x y) #Heq #_ lapply (Heq Hxy)
  -Heq #Heq destruct lapply (transitive_le … H2 H1) @le_Sn_n
| 4: #t * #y #HI #s #x #H whd in match (overline ? ?);
  change with (max ? ? ≤ ?) in H; lapply (HI s x (le_maxr … H))
  lapply (line_monotone_names) * #Hmono #_ lapply (Hmono t s)
  lapply four_dot_one_dot_one * #H411 #_ lapply (H411 t s (νx) (le_maxr … H))
  cases underline_pifTerm #c #n normalize #Hfv #Hsn -HI #HI
  cases neqb [1: >if_t // ]
  >if_f #H1 #H2 change with (fvb_t ? ? = fvb ? ?) in Hfv;
  cut (fvb_t (νx) t = false)
  [ lapply fresh_var_to_in * #Hfvtoin #_
    lapply (Hfvtoin … (transitive_le … (le_maxr … H) H1))
    lapply (fv_to_in_term) * -Hfvtoin #Hfvtoin #_
    @(bool_impl_inv2 Variable pifTerm Variable pifTerm inb_t fvb_t (νx) (νx) t t false false)
    @Hfvtoin
  ]
  >Hfv
  lapply (free_occ_to_fv_crumble) * * * * #Hfo #_ #_ #_ #_ lapply (Hfo c νx)
  * -Hfo #_ #Hfo @Hfo  
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply four_dot_one_dot_one * #H411t #H411v #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s #x
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s x)
      lapply (Hmono2 v1 s)
      lapply (H411v v1 s (νx) (le_maxl … H))
      cases (overline v1 s) #vv #n #Hfvv1 #Hsn normalize
      lapply (H2 n x)
      lapply (Hmono2 v2 n)
      lapply (H411v v2 n (νx) (transitive_le … (le_maxr … H) Hsn))
      cases (overline v2 n) #ww #m #Hfvv2 normalize #Hnm
      #H2' #H1'
      lapply (H2' (transitive_le … (le_maxr … H) Hsn)) -H2'
      lapply (H1' (le_maxl … H)) -H1' #H1' #H2' #HH #HHH
      cut (fvb_tv (νx) v1 = false)
      [ lapply fresh_var_to_in * #_ #Hfvtoin
      lapply (Hfvtoin … (transitive_le … (le_maxl … H) HH))
      lapply (fv_to_in_term) * -Hfvtoin #_ #Hfvtoin
      @(bool_impl_inv2 ???? inb_tv fvb_tv (νx) (νx) v1 v1 false false)
      @Hfvtoin
      ] >Hfvv1
      cut (fvb_tv (νx) v2 = false)
      [ lapply fresh_var_to_in * #_ #Hfvtoin
      lapply (Hfvtoin … (transitive_le … (le_maxr … H) HH))
      lapply (fv_to_in_term) * -Hfvtoin #_ #Hfvtoin
      @(bool_impl_inv2 ???? inb_tv fvb_tv (νx) (νx) v2 v2 false false)
      @Hfvtoin
      ] >Hfvv2 #Ha #Hb
      lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_ lapply (Hfo vv νx)
      * #_ #Hfo1 >Hfo1 // lapply (Hfo ww νx) * #_ #Hfo2 >Hfo2 //
    | #u1 #u2 normalize #H1 #H2 #s #x
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s x)
      lapply (Hbound (appl u1 u2) s)
      lapply (Hldom (appl u1 u2) s)
      lapply (Hmono1 (appl u1 u2) s)
      lapply (Hline1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hline1 #Hsn #Hldom1 #Hbound1 #H1'
      lapply (H2 n x)
      lapply (Hbound (val_to_term v2) n)
      lapply (Hldom (val_to_term v2) n) normalize
      lapply (Hmono2 v2 n)
      lapply (Hline2 v2 n)
      lapply (H411v v2 n (νx) (transitive_le … (le_maxr … H) Hsn))
      cases (overline v2 n) #vv #m #Hfvv2 normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hline2 #Hnm #Hldom2 #Hbound2 #H2'
    (* se n ≤ x < m x non è nè in b nè in e nè nel dominio di e, dunque la
        tesi diventa H2',
        se x = m 1≤1
        se s ≤ x ≤ n, allora domb_e = true , la tesi diventa molto simile ad H1'
        infatti le variabii di b, maggiorate da n possono al più essere catturate dal 
        dominio di e 
      *)
      
      
      >dom_push
      whd in match (domb_e ? (Cons ? ?));
      whd in match (veqb ? ?);
      >free_occ_push
      whd in match (free_occ_s ? ?);
      #Hsx #Hxm
      cut ((if if neqb x m then true else domb_e (νx) e  
            then O 
            else (if neqb x m then 1 else O )+free_occ_val (νx) vv =0))
      [ cut (neqb x m = true ∨ neqb x m = false) // * #Hxm >Hxm //
        >if_f >if_f cases domb_e // >if_f
        cut (fvb_tv (νx) v2 = false)
        [ lapply fresh_var_to_in * #_ #Hfvtoin
        lapply (Hfvtoin … (transitive_le … (le_maxr … H) Hsx))
        lapply (fv_to_in_term) * -Hfvtoin #_ #Hfvtoin
        @(bool_impl_inv2 ???? inb_tv fvb_tv (νx) (νx) v2 v2 false false)
        @Hfvtoin
        ] >Hfvv2 #Hf
        lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_ lapply (Hfo vv νx)
        * #_ #Hfo1 >Hfo1 //
      ] #H0 >H0 -H0
      whd in match (plus 0 ?);
      cut (leb n x = true ∨ leb n x = false) // * #Hnx
      [ lapply (leb_true_to_le … Hnx) -Hnx #Hnx
        cut (free_occ_e (νx) e=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #_ #He' #_ #_
          cut ((∀e0:Environment.∀x:Variable.inb_e x e0=false → fvb_e x e0=false))
          [ #e #x @(bool_impl_inv2 Variable Environment Variable Environment inb_e fvb_e x x e e false false)
            @He' 
          ] -He' #He'
          lapply (free_occ_to_fv_crumble) * * * * #_ #_ #He'' #_ #_
          lapply (He'' e νx) * #_ -He'' #He''
          @He'' @He' @He @(transitive_le … (le_maxr … (Hline1 (le_maxl … H))) Hnx)
        ]
        #HH1 >HH1
        cut (free_occ_b (νx) b=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #Hb' #_ #_ #_
          cut ((∀b.∀x:Variable.inb_b x b=false → fvb_b x b=false))
          [ #e #x @(bool_impl_inv2 Variable Byte Variable Byte inb_b fvb_b x x e e false false)
            @Hb' 
          ] -Hb' #Hb'
          lapply (free_occ_to_fv_crumble) * * * * #_ #Hb'' #_ #_ #_
          lapply (Hb'' b νx) * #_ -Hb'' #Hb''
          @Hb'' @Hb' @Hb @(transitive_le … (le_maxl … (Hline1 (le_maxl … H))) Hnx)
        ] #HH2 >HH2 cases domb_e  //
      | lapply (leb_false_to_not_le … Hnx) #Hlt
        lapply (not_le_to_lt … Hlt) -Hlt -Hnx normalize #Hnx
        lapply (H1' (le_maxl … H) Hsx Hnx) cases domb_e normalize //
      ]
    ]
  | #u1 #u2 normalize #H1 #H2 #s #x
    lapply (H2 s x)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hbound (appl u1 u2) s)
    lapply (Hldom (appl u1 u2) s)
    lapply (Hmono1 (appl u1 u2) s)
    lapply (Hline1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hbound (val_to_term v1) n)
      lapply (Hldom (val_to_term v1) n) normalize
      lapply (Hmono2 v1 n)
      lapply (Hline2 v1 n)
      lapply (H411v v1 n (νx))
      cases (overline v1 n) #vv #m
      normalize
      change with (fresh_var_tv ?)
        in match (pi1 ? ? (fresh_var_tv_Sig ?));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (max ? ?)
        in match (if ? then fresh_var_t ? else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e ? else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?); #Hfvv1
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2 #Hm
      #H
      lapply (H2 (le_maxr … Hm)) -H2 #H2
      lapply (H1 (transitive_le … (le_maxl … Hm) Hsn)) -H1 #H1
      >concat_epsilon_e >dom_push
      whd in match (domb_e ? (Cons ? ?));
      whd in match (veqb ? ?);
      >free_occ_push
      whd in match (free_occ_s ? ?); #Hxm
      cut ((if if neqb x m then true else domb_e (νx) e1  
            then O 
            else free_occ_val (νx) vv+(if neqb x m then 1 else O ) )=0)
      [ cut (neqb x m = true ∨ neqb x m = false) // * #Hxm >Hxm //
        >if_f >if_f cases domb_e // >if_f
        cut (fvb_tv (νx) v1 = false)
        [ lapply fresh_var_to_in * #_ #Hfvtoin
        lapply (Hfvtoin … (transitive_le … (le_maxl … Hm) H))
        lapply (fv_to_in_term) * -Hfvtoin #_ #Hfvtoin
        @(bool_impl_inv2 ???? inb_tv fvb_tv (νx) (νx) v1 v1 false false)
        @Hfvtoin
        ] change with (fvb_tv (νx) v1) in match (gtb ? 0) in Hfvv1;
        >(Hfvv1 (transitive_le … (le_maxl … Hm) Hsn)) #Hf
        lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_ lapply (Hfo vv νx)
        * #_ #Hfo1 >Hfo1 //
      ] #H0 >H0 -H0
      whd in match (0+?);
      cut (leb n x = true ∨ leb n x = false) // * #Hnx
      [ lapply (leb_true_to_le … Hnx) -Hnx #Hnx
        cut (free_occ_e (νx) e1=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #_ #He' #_ #_
          cut ((∀e0:Environment.∀x:Variable.inb_e x e0=false → fvb_e x e0=false))
          [ #e #x @(bool_impl_inv2 Variable Environment Variable Environment inb_e fvb_e x x e e false false)
            @He' 
          ] -He' #He'
          lapply (free_occ_to_fv_crumble) * * * * #_ #_ #He'' #_ #_
          lapply (He'' e1 νx) * #_ -He'' #He''
          @He'' @He' @He @(transitive_le … (le_maxr … (Hline2 (le_maxr … Hm))) Hnx)
        ]
        #HH1 >HH1
        cut (free_occ_b (νx) b1=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #Hb' #_ #_ #_
          cut ((∀b.∀x:Variable.inb_b x b=false → fvb_b x b=false))
          [ #e #x @(bool_impl_inv2 Variable Byte Variable Byte inb_b fvb_b x x e e false false)
            @Hb' 
          ] -Hb' #Hb'
          lapply (free_occ_to_fv_crumble) * * * * #_ #Hb'' #_ #_ #_
          lapply (Hb'' b1 νx) * #_ -Hb'' #Hb''
          @Hb'' @Hb' @Hb @(transitive_le … (le_maxl … (Hline2 (le_maxr … Hm))) Hnx)
        ] #HH2 >HH2 cases domb_e  //
      | lapply (leb_false_to_not_le … Hnx) #Hlt
        lapply (not_le_to_lt … Hlt) -Hlt -Hnx normalize #Hnx
        lapply (H2  H Hnx) cases domb_e normalize //
      ]
    | #r1 #r2 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hbound (appl r1 r2) n)
      lapply (Hldom (appl r1 r2) n)
      lapply (Hmono1 (appl r1 r2) n)
      lapply (Hline1 (appl r1 r2) n)
      lapply (H411t (appl r1 r2) n νx)
      change with (underline_pifTerm (appl r1 r2) n)
        in match ( match r2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl r1 r2) n ) * #b #e #m #H411
      normalize
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r2));
      change with (max ? ?)
        in match (if ? then fresh_var_t r2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_t u2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e1 else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?);
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1'
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2' #Hm
      #H
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      >domb_concat_distr >dom_push >dom_push
      whd in match (domb_e ? (Cons ? ?));
      whd in match (domb_e ? (Cons ? ?));
      change with (neqb ? ?) in match (veqb ? (νm));
      change with (neqb ? ?) in match (veqb ? (ν(S m)));
      >free_occ_concat >free_occ_push >free_occ_push
      whd in match (free_occ_s ? ?);
      whd in match (free_occ_s ? ?);
      whd in match (free_occ_s ? ?);
      >dom_push
      whd in match (domb_e ? (Cons ? ?));
      whd in match (veqb ? ?);
      cut ((if (if neqb x m then true else domb_e (νx) e1 
          ∨if neqb x (S m) then true else domb_e (νx) e ) 
          then O 
          else (if neqb x (S m) then 1 else O )+(if neqb x m then 1 else O ) )=0)
      [ cases neqb // >if_f >if_f cases neqb // >if_t >if_t
        change with (if ? then true else ?) in match (orb ? ?);
        >if_monotone //
      ] #H0 >H0 -H0 whd in match (0+(if ? then ? else ?));
      #Hxm
      cut (neqb x (S m) = true ∨ neqb x (S m) = false) // * #HxSm
      [ >HxSm >if_t
        cut (free_occ_e (ν(S m)) e=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #_ #He' #_ #_
          cut ((∀e0:Environment.∀x:Variable.inb_e x e0=false → fvb_e x e0=false))
          [ #e #x @(bool_impl_inv2 Variable Environment Variable Environment inb_e fvb_e x x e e false false)
            @He' 
          ] -He' #He'
          lapply (free_occ_to_fv_crumble) * * * * #_ #_ #He'' #_ #_
          lapply (He'' e ν(S m)) * #_ -He'' #He''
          @He'' @He' @He @(le_S … (le_maxr … (Hline1 (transitive_le … (le_maxl … Hm) Hsn))))
        ]
        #HH1
        cut (free_occ_b (ν(S m)) b=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #Hb' #_ #_ #_
          cut ((∀b.∀x:Variable.inb_b x b=false → fvb_b x b=false))
          [ #e #x @(bool_impl_inv2 Variable Byte Variable Byte inb_b fvb_b x x e e false false)
            @Hb' 
          ] -Hb' #Hb'
          lapply (free_occ_to_fv_crumble) * * * * #_ #Hb'' #_ #_ #_
          lapply (Hb'' b ν(S m)) * #_ -Hb'' #Hb''
          @Hb'' @Hb' @Hb @(le_S … (le_maxl … (Hline1 (transitive_le … (le_maxl … Hm) Hsn))))
        ] #HH2
        elim (neqb_iff_eq x (S m)) #Heq #_ lapply (Heq HxSm) -Heq #Heq destruct
        >HH1 >HH2 whd in match (0+0); >if_monotone //
      ]
      cut (leb n x = true ∨ leb n x = false) // * #Hnx
      [ lapply (leb_true_to_le … Hnx) -Hnx #Hnx
        cut (free_occ_e (νx) e1=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #_ #He' #_ #_
          cut ((∀e0:Environment.∀x:Variable.inb_e x e0=false → fvb_e x e0=false))
          [ #e #x @(bool_impl_inv2 Variable Environment Variable Environment inb_e fvb_e x x e e false false)
            @He' 
          ] -He' #He'
          lapply (free_occ_to_fv_crumble) * * * * #_ #_ #He'' #_ #_
          lapply (He'' e1 νx) * #_ -He'' #He''
          @He'' @He' @He @(transitive_le … (le_maxr … (Hline2 (le_maxr … Hm))) Hnx)
        ]
        #HH1 >HH1
        cut (free_occ_b (νx) b1=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #Hb' #_ #_ #_
          cut ((∀b.
          ∀x:Variable.inb_b x b=false → fvb_b x b=false))
          [ #e #x @(bool_impl_inv2 Variable Byte Variable Byte inb_b fvb_b x x e e false false)
            @Hb' 
          ] -Hb' #Hb'
          lapply (free_occ_to_fv_crumble) * * * * #_ #Hb'' #_ #_ #_
          lapply (Hb'' b1 νx) * #_ -Hb'' #Hb''
          @Hb'' @Hb' @Hb @(transitive_le … (le_maxl … (Hline2 (le_maxr … Hm))) Hnx)
        ] #HH2 >HH2
        whd in match (0+0);
        >if_monotone whd in match (0+ (if (domb_e ? e) then ? else ?));
        >if_monotone
        cut (x ≤ S m) [/2/] #HxSm'
        cut (x ≤ m)
        [ @le_S_S_to_le  @le_to_neqb_to_lt // ]
         -HxSm'
        cut (neqb x (m) = true ∨ neqb x (m) = false) // * #Hxm1
        [ cut (free_occ_e (νm) e=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #_ #He #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #_ #He' #_ #_
          cut ((∀e0:Environment.∀x:Variable.inb_e x e0=false → fvb_e x e0=false))
          [ #e #x @(bool_impl_inv2 Variable Environment Variable Environment inb_e fvb_e x x e e false false)
            @He' 
          ] -He' #He'
          lapply (free_occ_to_fv_crumble) * * * * #_ #_ #He'' #_ #_
          lapply (He'' e ν(m)) * #_ -He'' #He''
          @He'' @He' @He @((le_maxr … (Hline1 (transitive_le … (le_maxl … Hm) Hsn))))
        ]
        #HH1
        cut (free_occ_b (ν(m)) b=0)
        [ lapply fresh_var_to_in_crumble * * * * #_ #Hb #_ #_ #_
          lapply (fv_to_in_crumble) * * * * #_ #Hb' #_ #_ #_
          cut ((∀b.∀x:Variable.inb_b x b=false → fvb_b x b=false))
          [ #e #x @(bool_impl_inv2 Variable Byte Variable Byte inb_b fvb_b x x e e false false)
            @Hb' 
          ] -Hb' #Hb'
          lapply (free_occ_to_fv_crumble) * * * * #_ #Hb'' #_ #_ #_
          lapply (Hb'' b ν(m)) * #_ -Hb'' #Hb''
          @Hb'' @Hb' @Hb @((le_maxl … (Hline1 (transitive_le … (le_maxl … Hm) Hsn))))
        ] #HH2
        elim (neqb_iff_eq x (m)) #Heq #_ lapply (Heq Hxm1) -Heq #Heq destruct
        >HH1 >HH2 whd in match (0+0); >if_monotone //
      ]
      -Hxm #Hxm
      cut (x < m)
      [ @le_to_neqb_to_lt // ] -Hxm #Hxm
      lapply (H1' Hnx Hxm) cases domb_e // >if_f >if_f //
    | >HxSm normalize
      lapply (leb_false_to_not_le … Hnx) -Hnx #Hnx
      lapply (not_le_to_lt … Hnx) -Hnx #Hnx
      cut (fresh_var_t (appl r1 r2)≤n)
      [ change with (max ? ? ≤ n)
        @(transitive_le … (le_maxl … Hm) Hsn) ]
      #HH lapply (H411 HH) -HH -H411 #H411
      cut (fvb_t (νx) (appl r1 r2)= false)
      [ normalize
        cut (free_occ_t (νx) r1=0)
        [ lapply (free_occ_to_fv νx) * #Hfo #_ lapply (Hfo r1) * #_ -Hfo #Hfo
          @Hfo elim fresh_var_to_in #Hfv #_
          lapply (Hfv … (transitive_le … (le_maxl … (le_maxl … Hm)) H)) -Hfv 
          elim (fv_to_in_term) #Hfv #_
          @(bool_impl_inv2 ???? inb_t fvb_t ???? false false (Hfv …))
        ] #Hr1
        cut (free_occ_t (νx) r2=0)
        [ lapply (free_occ_to_fv νx) * #Hfo #_ lapply (Hfo r2) * #_ -Hfo #Hfo
          @Hfo elim fresh_var_to_in #Hfv #_
          lapply (Hfv … (transitive_le … (le_maxr … (le_maxl … Hm)) H)) -Hfv 
          elim (fv_to_in_term) #Hfv #_
          @(bool_impl_inv2 ???? inb_t fvb_t ???? false false (Hfv …))
        ] #Hr2 >Hr1 >Hr2 //
      | >H411 whd in match (fvb ? ?);
        cases domb_e
        [ normalize >if_monotone >if_f
          lapply (free_occ_to_fv_crumble) * * * * #_ #_ #Hfo #_ #_
          lapply (Hfo e (νx)) * #_ -Hfo #Hfo #Hfvb >(Hfo Hfvb) //
        | normalize >if_then_true_else_false #HH
          cut (fvb_b (νx) b = false)
          [ lapply HH cases fvb_b // >if_t #H @H ]
          cut (fvb_e (νx) e = false)
          [ lapply HH cases fvb_e // >if_monotone #H @H ]
           #Hfe #Hfb
          cut (free_occ_b (νx) b = 0)
          [ lapply (free_occ_to_fv_crumble) * * * * #_ #Hfo #_ #_ #_
            lapply (Hfo b (νx)) * #_ -Hfo #Hfo @Hfo // ]
          -Hfb #Hfb >Hfb
          cut (free_occ_e (νx) e = 0)
          [ lapply (free_occ_to_fv_crumble) * * * * #_ #_ #Hfo #_ #_
            lapply (Hfo e (νx)) * #_ -Hfo #Hfo @Hfo // ]
          -Hfe #Hfe >Hfe
          whd in match (0+0);
          lapply (H2' H Hnx) cases domb_e normalize //
        ]
      ]
    ]
  ]
] qed.
*)
(*
lemma dom_var_occ: 
 (∀t, s, x.
  fresh_var_t t ≤ s →
   domb x (fst … (underline_pifTerm t s)) = true →
    free_occ_b x match (fst … (underline_pifTerm t s)) with 
     [ CCrumble b e ⇒ b] ≤ 1) ∧
 (∀v:pifValue. True).

@pifValueTerm_ind
[ #v #_ #s #x normalize cases overline #vv #n normalize #_ #abs destruct
| 3: //
| 4: //
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply four_dot_one_dot_one * #H411t #H411v #t1 #t2 cases t2  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s #x
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s x)
      lapply (Hmono2 v1 s)
      cases (overline v1 s) #vv #n normalize #Hsn #H1'
      lapply (H2 n x)
      lapply (Hmono2 v2 s)
      cases (overline v2 n) #ww #m normalize #Hnm #H2'
      #abs destruct
    | #u1 #u2 normalize #H1 #H2 #s #x
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s x)
      lapply (Hbound (appl u1 u2) s)
      lapply (Hldom (appl u1 u2) s)
      lapply (Hmono1 (appl u1 u2) s)
      lapply (Hline1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hline1 #Hsn #Hldom1 #Hbound1 #H1'
      lapply (H2 n x)
      lapply (Hbound (val_to_term v2) n)
      lapply (Hldom (val_to_term v2) n) normalize
      lapply (Hmono2 v2 n)
      lapply (Hline2 v2 n)
      lapply (H411v v2 n x (transitive_le … (le_maxr … H) Hsn))
      cases (overline v2 n) #vv #m #Hfvv2 normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hline2 #Hnm #Hldom2 #Hbound2 #H2'
      >dom_push whd in match (domb_e ? ?);

      cut (veqb x (νm) = true ∨ veqb x (νm) = false) // * #Hxm
      [ elim (veqb_true_to_eq x νm) #Heq #_ lapply (Heq Hxm) -Heq #Heq
        destruct >Hxm >if_t >if_t #_
        lapply (Hline2 (transitive_le … (le_maxr … H) Hsn))
        lapply fresh_var_to_in_crumble * * * * #_#_#_ #Hfv #_
        #HH lapply (Hfv … HH) -HH #HH -Hfv
        lapply fv_to_in_crumble * * * * #_#_#_ #Hfv #_
        cut (inb_v (νm) vv=false → fvb_v (νm) vv = false)
        [ @(bool_impl_inv2  ???? inb_v fvb_v (νm) (νm) vv vv false false) @Hfv ]
        -Hfv #Hfv lapply (Hfv HH) -Hfv -HH #HH
        lapply free_occ_to_fv_crumble * * * * #_ #_ #_ #Hfv #_
        lapply (Hfv vv νm) * #_ #Hfv lapply (Hfv HH) -HH #HH >HH //
      | >Hxm >if_f >if_f #Hdome
        cut (fvb_tv (x) v2 = false)
        [ lapply Hdome cases x #nx lapply fresh_var_to_in * #_ #Hfvtoin -Hdome
          #Hdome
        lapply (Hfvtoin … (transitive_le … (le_maxr … H) (Hldom1 … Hdome)))
        lapply (fv_to_in_term) * -Hfvtoin #_ #Hfvtoin
        @(bool_impl_inv2 ???? inb_tv fvb_tv (νnx) (νnx) v2 v2 false false)
        @Hfvtoin
        ] >Hfvv2 #Hf
        lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_ lapply (Hfo vv x)
        * #_ #Hfo1 >Hfo1 //
      ]
    ]
    | #u1 #u2 normalize #H1 #H2 #s #x
    lapply (H2 s x)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hbound (appl u1 u2) s)
    lapply (Hldom (appl u1 u2) s)
    lapply (Hmono1 (appl u1 u2) s)
    lapply (Hline1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hbound (val_to_term v1) n)
      lapply (Hldom (val_to_term v1) n) normalize
      lapply (Hmono2 v1 n)
      lapply (Hline2 v1 n)
      lapply (H411v v1 n (x))
      cases (overline v1 n) #vv #m
      normalize
      change with (fresh_var_tv ?)
        in match (pi1 ? ? (fresh_var_tv_Sig ?));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (max ? ?)
        in match (if ? then fresh_var_t ? else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e ? else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?); #Hfvv1
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2 #Hm
      #H
      lapply (H2 (le_maxr … Hm)) -H2 #H2
      lapply (H1 (transitive_le … (le_maxl … Hm) Hsn)) -H1 #H1
      lapply H
      >concat_epsilon_e >dom_push
      whd in match (domb_e ? (Cons ? ?));
      cut (veqb x (νm) = true ∨ veqb x (νm) = false) // * #Hxm
      [ elim (veqb_true_to_eq x νm) #Heq #_ lapply (Heq Hxm) -Heq #Heq
        destruct >veqb_true >if_t #_ >if_t
        cut (free_occ_val (νm) vv =0)
        [ lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_
          lapply (Hfo vv νm) * #_ -Hfo #Hfo @Hfo -Hfo
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hfo #_
          @(bool_impl_inv2 ???? inb_v fvb_v (νm) (νm) vv vv false false)
          [ lapply (fv_to_in_crumble) * * * * #_ #_ #_ #Hfo' #_ @Hfo' ]
          @Hfo @Hline1 @(transitive_le …(le_maxl … Hm) Hsn) ]
        #HH >HH // ]
      >Hxm >if_f >if_f
      cut (fvb_tv x v1 = false)
      [ elim (fv_to_in_term) #_  #Hfv lapply (Hfv v1) -Hfv #Hfv
        @(bool_impl_inv2 ???? inb_tv fvb_tv x x v1 v1 false false) [ @Hfv ]
        lapply (fresh_var_to_in) * #_ -Hfv #Hfv lapply H lapply Hxm
        elim x #nx #Hxm' #H' @Hfv
        lapply H' >concat_epsilon_e >dom_push whd in match (domb_e ? ?);
        >Hxm' >if_f #Hdome1 lapply (Hldom2 … Hdome1) #Hsnx
        @(transitive_le … (le_maxl … Hm) Hsnx) ]
      change with (gtb ? 0) in match (fvb_tv x v1); 
      >(Hfvv1 (transitive_le … (le_maxl … Hm) Hsn)) #Hvv #_
      cut (free_occ_val x vv = 0)
      [ lapply free_occ_to_fv_crumble * * * * #_ #_ #_ #Hfo #_
        lapply (Hfo vv x) * #_ -Hfo #Hfo @Hfo //
      ]  #HH >HH //
    | #r1 #r2 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hbound (appl r1 r2) n)
      lapply (Hldom (appl r1 r2) n)
      lapply (Hmono1 (appl r1 r2) n)
      lapply (Hline1 (appl r1 r2) n)
      lapply (H411t (appl r1 r2) n x)
      change with (underline_pifTerm (appl r1 r2) n)
        in match ( match r2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl r1 r2) n ) * #b #e #m #H411
      normalize
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r2));
      change with (max ? ?)
        in match (if ? then fresh_var_t r2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_t u2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e1 else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?);
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1'
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2' #Hm
      #H
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      cut (veqb x (ν(S m)) = true ∨ veqb x (ν(S m)) = false) // * #HxSm
      [ >HxSm >if_t elim (veqb_true_to_eq x ν(S m)) #Heq #_
        lapply (Heq HxSm) -Heq #Heq destruct
        change with (neqb ? ?) in match (veqb ? ?); >neq_simm 
        >neqb_false normalize //
      | >HxSm >if_f cases veqb //
      ]
    ]
  ]
] qed.

lemma dom_var_occ: 
 (∀t, s, b, e, x, b'.
  fresh_var_t t ≤ s →
   (fst … (underline_pifTerm t s)) = 〈b, Cons e [x ←b']〉 →
    free_occ x (CCrumble b e) = 1) ∧
 (∀v:pifValue. True).

@pifValueTerm_ind
[ #v #_ #s #b #e #x #b' normalize cases overline #vv #n normalize #_ #abs destruct
| 3: //
| 4: //
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply four_dot_one_dot_one * #H411t #H411v #t1 #t2 cases t2  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s #b #e #x #b'
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s)
      lapply (Hmono2 v1 s)
      cases (overline v1 s) #vv #n normalize #Hsn #H1'
      lapply (H2 n)
      lapply (Hmono2 v2 s)
      cases (overline v2 n) #ww #m normalize #Hnm #H2'
      #abs destruct
    | #u1 #u2 normalize #H1 #H2 #s #b #e #x #b'
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s)
      lapply (Hbound (appl u1 u2) s)
      lapply (Hldom (appl u1 u2) s)
      lapply (Hmono1 (appl u1 u2) s)
      lapply (Hline1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #d #f #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hline1 #Hsn #Hldom1 #Hbound1 #H1'
      lapply (H2 n)
      lapply (Hbound (val_to_term v2) n)
      lapply (Hldom (val_to_term v2) n) normalize
      lapply (Hmono2 v2 n)
      lapply (Hline2 v2 n)
      lapply (H411v v2 n x (transitive_le … (le_maxr … H) Hsn))
      cases (overline v2 n) #vv #m #Hfvv2 normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hline2 #Hnm #Hldom2 #Hbound2 #H2' #HH
      cases f
      [ whd in match (push ? ?); destruct normalize >neqb_refl >if_t
      | #ff #ss whd in match (push ? ?);
        -e0 #e0 destruct
        >dom_push >free_occ_push
        whd in match (free_occ_s ? ?); ]
      
      >dom_push whd in match (domb_e ? ?);

      cut (veqb x (νm) = true ∨ veqb x (νm) = false) // * #Hxm
      [ elim (veqb_true_to_eq x νm) #Heq #_ lapply (Heq Hxm) -Heq #Heq
        destruct >Hxm >if_t >if_t #_
        lapply (Hline2 (transitive_le … (le_maxr … H) Hsn))
        lapply fresh_var_to_in_crumble * * * * #_#_#_ #Hfv #_
        #HH lapply (Hfv … HH) -HH #HH -Hfv
        lapply fv_to_in_crumble * * * * #_#_#_ #Hfv #_
        cut (inb_v (νm) vv=false → fvb_v (νm) vv = false)
        [ @(bool_impl_inv2  ???? inb_v fvb_v (νm) (νm) vv vv false false) @Hfv ]
        -Hfv #Hfv lapply (Hfv HH) -Hfv -HH #HH
        lapply free_occ_to_fv_crumble * * * * #_ #_ #_ #Hfv #_
        lapply (Hfv vv νm) * #_ #Hfv lapply (Hfv HH) -HH #HH >HH //
      | >Hxm >if_f >if_f #Hdome
        cut (fvb_tv (x) v2 = false)
        [ lapply Hdome cases x #nx lapply fresh_var_to_in * #_ #Hfvtoin -Hdome
          #Hdome
        lapply (Hfvtoin … (transitive_le … (le_maxr … H) (Hldom1 … Hdome)))
        lapply (fv_to_in_term) * -Hfvtoin #_ #Hfvtoin
        @(bool_impl_inv2 ???? inb_tv fvb_tv (νnx) (νnx) v2 v2 false false)
        @Hfvtoin
        ] >Hfvv2 #Hf
        lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_ lapply (Hfo vv x)
        * #_ #Hfo1 >Hfo1 //
      ]
    ]
    | #u1 #u2 normalize #H1 #H2 #s #x
    lapply (H2 s x)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hbound (appl u1 u2) s)
    lapply (Hldom (appl u1 u2) s)
    lapply (Hmono1 (appl u1 u2) s)
    lapply (Hline1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hbound (val_to_term v1) n)
      lapply (Hldom (val_to_term v1) n) normalize
      lapply (Hmono2 v1 n)
      lapply (Hline2 v1 n)
      lapply (H411v v1 n (x))
      cases (overline v1 n) #vv #m
      normalize
      change with (fresh_var_tv ?)
        in match (pi1 ? ? (fresh_var_tv_Sig ?));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (max ? ?)
        in match (if ? then fresh_var_t ? else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e ? else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?); #Hfvv1
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2 #Hm
      #H
      lapply (H2 (le_maxr … Hm)) -H2 #H2
      lapply (H1 (transitive_le … (le_maxl … Hm) Hsn)) -H1 #H1
      lapply H
      >concat_epsilon_e >dom_push
      whd in match (domb_e ? (Cons ? ?));
      cut (veqb x (νm) = true ∨ veqb x (νm) = false) // * #Hxm
      [ elim (veqb_true_to_eq x νm) #Heq #_ lapply (Heq Hxm) -Heq #Heq
        destruct >veqb_true >if_t #_ >if_t
        cut (free_occ_val (νm) vv =0)
        [ lapply (free_occ_to_fv_crumble) * * * * #_ #_ #_ #Hfo #_
          lapply (Hfo vv νm) * #_ -Hfo #Hfo @Hfo -Hfo
          lapply (fresh_var_to_in_crumble) * * * * #_ #_ #_ #Hfo #_
          @(bool_impl_inv2 ???? inb_v fvb_v (νm) (νm) vv vv false false)
          [ lapply (fv_to_in_crumble) * * * * #_ #_ #_ #Hfo' #_ @Hfo' ]
          @Hfo @Hline1 @(transitive_le …(le_maxl … Hm) Hsn) ]
        #HH >HH // ]
      >Hxm >if_f >if_f
      cut (fvb_tv x v1 = false)
      [ elim (fv_to_in_term) #_  #Hfv lapply (Hfv v1) -Hfv #Hfv
        @(bool_impl_inv2 ???? inb_tv fvb_tv x x v1 v1 false false) [ @Hfv ]
        lapply (fresh_var_to_in) * #_ -Hfv #Hfv lapply H lapply Hxm
        elim x #nx #Hxm' #H' @Hfv
        lapply H' >concat_epsilon_e >dom_push whd in match (domb_e ? ?);
        >Hxm' >if_f #Hdome1 lapply (Hldom2 … Hdome1) #Hsnx
        @(transitive_le … (le_maxl … Hm) Hsnx) ]
      change with (gtb ? 0) in match (fvb_tv x v1); 
      >(Hfvv1 (transitive_le … (le_maxl … Hm) Hsn)) #Hvv #_
      cut (free_occ_val x vv = 0)
      [ lapply free_occ_to_fv_crumble * * * * #_ #_ #_ #Hfo #_
        lapply (Hfo vv x) * #_ -Hfo #Hfo @Hfo //
      ]  #HH >HH //
    | #r1 #r2 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hbound (appl r1 r2) n)
      lapply (Hldom (appl r1 r2) n)
      lapply (Hmono1 (appl r1 r2) n)
      lapply (Hline1 (appl r1 r2) n)
      lapply (H411t (appl r1 r2) n x)
      change with (underline_pifTerm (appl r1 r2) n)
        in match ( match r2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl r1 r2) n ) * #b #e #m #H411
      normalize
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig u2));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r1));
      change with (fresh_var_t ?)
        in match (pi1 ? ? (fresh_var_t_Sig r2));
      change with (max ? ?)
        in match (if ? then fresh_var_t r2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_t u2 else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e else ?);
      change with (max ? ?)
        in match (if ? then fresh_var_e e1 else ?);
      change with (max ? ?)
        in match (if ? then max ? ? else ?);
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1'
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2' #Hm
      #H
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      cut (veqb x (ν(S m)) = true ∨ veqb x (ν(S m)) = false) // * #HxSm
      [ >HxSm >if_t elim (veqb_true_to_eq x ν(S m)) #Heq #_
        lapply (Heq HxSm) -Heq #Heq destruct
        change with (neqb ? ?) in match (veqb ? ?); >neq_simm 
        >neqb_false normalize //
      | >HxSm >if_f cases veqb //
      ]
    ]
  ]
] qed.

let rec aux_read_back rbb e on e ≝
 match e with
 [ Epsilon ⇒ rbb
 | Cons e1 s ⇒ match s with [ subst x' b1 ⇒ pif_subst (aux_read_back rbb e1) (psubst x' (read_back_b b1))]
 ]

and

read_back_b b ≝
 match b with
 [ CValue v ⇒ read_back_v v
 | AppValue v w ⇒ appl (read_back_v v) (read_back_v w)
 ]

and

read_back_v v ≝
 match v with
 [ var x ⇒ val_to_term (pvar x)
 | lambda x c ⇒ match c with
                [ CCrumble b e ⇒ val_to_term (abstr x (aux_read_back (read_back_b b) e))]
 ]
 .

let rec read_back c on c ≝
 match c with
 [ CCrumble b e ⇒ aux_read_back (read_back_b b) e]
 .
*)