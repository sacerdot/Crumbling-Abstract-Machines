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

include "underline_readback.ma".

let rec dist_dom e on e ≝ 
 match e with
  [ Epsilon ⇒ true
  | Cons e s ⇒ (¬domb_e match s with [subst y b ⇒ y] e) ∧ dist_dom e
  ].
  
let rec well_named c on c ≝
 match c with
 [ CCrumble b e ⇒ well_named_b b ∧ well_named_e e ∧ dist_dom e]
 
and well_named_b b on b ≝
 match b with
 [ CValue v ⇒ well_named_v v
 | AppValue v w ⇒ (well_named_v v) ∧ (well_named_v w)
 ]
 
and well_named_v v on v ≝
 match v with
 [ var x ⇒ true
 | lambda x c ⇒ well_named c
 ]  

and well_named_e e on e ≝
 match e with
 [ Epsilon ⇒ true
 | Cons e s ⇒ (well_named_e e) ∧ (well_named_s s)
 ]
 
and well_named_s s on s ≝
 match s with
 [ subst y b ⇒ well_named_b b ]
.

lemma dist_dom_push: ∀e, s. dist_dom (push e s) = dist_dom (Cons e s).

@Environment_simple_ind2
[ normalize //
| #e * #y #b #H * #y' #b'
  whd in match (push ? ?);
  whd in match (dist_dom (Cons ? ?));
  whd in match (dist_dom (Cons (Cons ? ?) ?));
  >H normalize >dom_push
  whd in match (domb_e ? ?);
  >veqb_comm cases veqb normalize //
  cases domb_e normalize //
  >if_monotone //
] qed.

lemma well_named_push: ∀e, s. well_named_e (push e s) = well_named_e (Cons e s).

@Environment_simple_ind2
[ normalize //
| #e #s #H * #y #b
  whd in match (push ? ?);
  whd in match (well_named_e (Cons ? ?));
  whd in match (well_named_e (Cons (Cons ? ?) ?));
  >H normalize cases well_named_e normalize //
  cases well_named_b normalize
  [ >if_then_true_else_false | >if_monotone ] //
] qed.

lemma dist_dom_conservative: ∀e, s. dist_dom (Cons e s) =true → dist_dom e=true.
@Environment_simple_ind2
[ #s normalize //
| #e * #y #b #H * #y' #b'
  whd in match (dist_dom ?);
  whd in match (match ? return λ_:Substitution.Variable with 
         [subst (y0:Variable)   (b0:Byte)⇒y0]);
  lapply (H ([y←b]))
  cases (dist_dom (Cons e [y←b])) //
  >if_monotone #_ #abs destruct
] qed.

lemma well_named_concat:
 ∀f, e. well_named_e (concat e f) = (well_named_e e ∧ well_named_e f).

@Environment_simple_ind2
[ #e >concat_e_epsilon normalize >if_then_true_else_false //
| #f #s #H #e
  whd in match (concat ? ?);
  whd in match (well_named_e ?);
  >H
  whd in match (well_named_e (Cons ? ?));
  cases well_named_e normalize //
] qed.

lemma dist_dom_lemma:
 ∀e1,e,s,m,n,b,b1.
  s≤n → n≤m → 
   (∀x:ℕ.domb_e (νx) e1=true→s≤x) → 
    (∀x:ℕ.domb_e (νx) e1=true→S x≤n) → 
     (∀x:ℕ.domb_e (νx) e=true→n≤x) → 
      (∀x:ℕ.domb_e (νx) e=true→S x≤m) → 
       dist_dom e=true → dist_dom e1=true → 
        dist_dom (concat (push e [ν(S m)←b]) (push e1 [νm←b1]))=true .

@Environment_simple_ind2
[ #e #s #m #n #b #b1 #Hsn #Hnm #Hl1 #Hu1 #Hl2 #Hu2 #Hde #Hde1
  whd in match (push Epsilon ?);
  whd in match (concat ? ?); whd in match (dist_dom ?);
  >concat_e_epsilon
  whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
  >dom_push >dist_dom_push
  whd in match (domb_e ? ?);
  whd in match (dist_dom ?);
  whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
  change with (neqb ? ?) in match (veqb ? ?);
  >neqb_false >if_f
  cut (∀x:ℕ.m≤x → domb_e (νx) e=false)
  [ #x lapply (Hu2 x) cases domb_e // #abs1 #abs2 @False_ind
    lapply (transitive_le … (abs1 (refl bool true)) abs2) /2/ ]
    #Hu1' >Hu1' >Hu1' // normalize @Hde
| #f * #y #b #HI #e #s #m #n #b #b1 #Hsn #Hnm #Hl1 #Hu1 #Hl2 #Hu2 #Hde #Hde1
  whd in match (push (Cons ? ?) ?);
  whd in match (concat ? ?);
  whd in match (dist_dom ?);
  whd in match (match ? in Substitution with [_⇒?]);
  >domb_concat_distr >dom_push >dom_push

   >(HI … s m n)
  [ 2: @(dist_dom_conservative … Hde1) | 3: @Hde  @Hu1
  | 4: @Hu2 | 8: @Hnm | 9: @Hsn| 5: @Hl2
  | 6: #k #Hk @Hu1 normalize >Hk >if_monotone @refl
  | 7: #k #Hk @Hl1 normalize >Hk >if_monotone @refl ]
  >if_then_true_else_false
  whd in match (domb_e ? ?);
  whd in match (domb_e ? (Cons ? ?));
  cut (veqb y (νm)=true ∨ veqb y (νm)=false) // * #Hym
  [ elim (veqb_true_to_eq y (νm)) #Heq #_ lapply (Heq Hym)
    -Heq #Heq destruct @False_ind lapply (transitive_le … (Hu1 m ?) Hnm)
    [ normalize >neqb_refl >if_t @refl ] @le_Sn_n
  | >Hym >if_f cut (veqb y (ν(S m))=true ∨ veqb y (ν(S m))=false) // * #HySm
  [ elim (veqb_true_to_eq y (ν(S m))) #Heq #_ lapply (Heq HySm)
    -Heq #Heq destruct @False_ind lapply (le_S … (transitive_le … (Hu1 (S m) ?) Hnm))
    [ normalize >neqb_refl >if_t @refl ] @le_Sn_n
  | >HySm  lapply (Hde1) -Hde1 lapply (Hl1) -Hl1 lapply (Hu1) -Hu1
    cases y #ny normalize #Hu1 #Hl1 lapply (Hl1 ny) lapply (Hu1 ny)
    cases domb_e normalize [ #_ #_ #abs destruct ] >neqb_refl >if_t #Hu1 #_ #_
    lapply (Hl2 ny) cases domb_e // #Hye @False_ind
    lapply (transitive_le … (Hu1 (refl …)) (Hye (refl …)))
    @le_Sn_n
  ] ]
] qed.
  
lemma four_dot_one_dot_four:

 (∀(t: pifTerm).
   ∀(s:nat). fresh_var_t t ≤ s →
    well_named (fst … (underline_pifTerm t s))=true) ∧
 (∀(v: pifValue).
   ∀(s:nat). fresh_var_tv v ≤ s →
    well_named (fst … (underline_pifTerm (val_to_term v) s))=true).
  
@pifValueTerm_ind
[ #v #H @H
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply (free_var_bound) * #Hfvbd1 #Hfvbd2 #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s)
      lapply (Hmono2 v1 s)
      cases (overline v1 s) #vv #n normalize #Hsn
      >if_then_true_else_false >if_then_true_else_false #H1'
      lapply (H2 n)
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #ww #m normalize #Hnm
      >if_then_true_else_false >if_then_true_else_false #H2'
      >if_then_true_else_false >if_then_true_else_false
      >(H1' (le_maxl … H)) >(H2' (transitive_le … (le_maxr … H) Hsn)) //
    | #u1 #u2 normalize #H1 #H2 #s
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
      cases (overline v2 n) #vv #m normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hline2 #Hnm #Hldom2 #Hbound2
      >if_then_true_else_false >if_then_true_else_false #H2'
      >(H2' (transitive_le … (le_maxr … H) Hsn)) >if_t
      >well_named_push >dist_dom_push
      whd in match (well_named_e ?);
      whd in match (well_named_s ?);
      whd in match (dist_dom ?);
      whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
      cut (∀x:ℕ.n≤x → domb_e (νx) e=false)
      [ #x lapply (Hbound1 x) cases domb_e // #abs1 #abs2 @False_ind
        lapply (transitive_le … (abs1 (refl bool true)) abs2) /2/ ]
      #Hbound1' >Hbound1' //
      whd in match (¬false); >if_t lapply (H1' (le_maxl … H))
      cases dist_dom [ 2: >if_monotone  >if_monotone // ]
      cases well_named_b normalize
      cases well_named_e normalize //
    ]
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
        in match (if ? then max ? ? else ?);
      #Hline1 #Hnm #Hldom1 #Hbound1
      #H1
      #Hline2 #Hsn #Hldom2 #Hbound2
      #H2 #Hm
      lapply (H2 (le_maxr … Hm)) -H2 #H2
      lapply (H1 (transitive_le … (le_maxl … Hm) Hsn)) -H1
      >if_then_true_else_false >if_then_true_else_false #H1
      >H1 normalize
      >concat_epsilon_e >well_named_push >dist_dom_push
      whd in match (well_named_e ?);
      whd in match (well_named_e ?);
      whd in match (well_named_s ?);
      whd in match (dist_dom ?);
      whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
      cut (∀x:ℕ.n≤x → domb_e (νx) e1=false)
      [ #x lapply (Hbound2 x) cases domb_e // #abs1 #abs2 @False_ind
        lapply (transitive_le … (abs1 (refl bool true)) abs2) /2/ ]
      #Hbound2' >Hbound2' // whd in match (¬false); >if_t
      lapply H2 cases dist_dom cases well_named_b cases well_named_e //
    | #r1 #r2 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hbound (appl r1 r2) n)
      lapply (Hldom (appl r1 r2) n)
      lapply (Hmono1 (appl r1 r2) n)
      lapply (Hline1 (appl r1 r2) n)
      change with (underline_pifTerm (appl r1 r2) n)
        in match ( match r2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl r1 r2) n ) * #b #e #m
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
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      >well_named_concat >well_named_push >well_named_push
      whd in match (well_named_e ?);
      whd in match (well_named_e (Cons e [ν(S m)←?]));
      whd in match (well_named_s ?);
      whd in match (well_named_s ?);
      
      lapply H1' lapply H2'
      cases (well_named_b b1)
      cases (well_named_e e1)
      cases (well_named_b b)
      cases (well_named_e e)
      normalize // [ 2,3,4: #abs destruct ] 
      #Hdom1 #Hdom2
      >dist_dom_lemma
      [ lapply H2' >Hdom1 cases well_named_e cases well_named_b normalize #H @H
      | @Hdom1
      | @Hdom2
      | @Hbound1
      | @Hldom1
      | @Hbound2
      | @Hldom2
      | @Hnm
      | @Hsn
      | skip
      | skip
      ]
    ]
  ]
| #y #x #s normalize //
| #t * #x #H #s
  change with (max (S x) (fresh_var_t ?)) in match (fresh_var_tv ?); #Hm
  lapply (H s (le_maxr … Hm)) normalize cases underline_pifTerm * #b #e #n
  normalize >if_then_true_else_false >if_then_true_else_false #h' @h'
] qed.

definition w_well_named ≝ λc. 
 match c with
 [CCrumble b e ⇒ dist_dom e ].
 
lemma well_named_relax: ∀c. well_named c=true → w_well_named c=true.
* #b #e normalize cases well_named_b cases well_named_e normalize //
#abs destruct qed.

lemma dist_dom_s_dom: ∀e, y, b. dist_dom (Cons e [y←b]) =true → domb_e y e =false.

@Environment_simple_ind2
[ #y #b normalize //
| #e * #y' #b' #H #y #b lapply (H y b) -H #HI
  normalize
  cut (veqb y y' = true ∨ veqb y y' = false) // * #Hyy'
  [ elim(veqb_true_to_eq y y') #Heq #_ lapply (Heq Hyy') -Heq #Heq destruct
    >Hyy' normalize #H >H @refl
  | >Hyy' >if_f cases domb_e
    [ normalize #H >H @refl
    | #_ @refl
    ]
  ]
] qed.

lemma dist_dom_concat:
 ∀e, f. dist_dom (concat e f) =true →
  dist_dom e = true ∧ dist_dom f = true.

#e @Environment_simple_ind2
[ normalize #H >H % @refl
| #f #s
  whd in match (concat ? (Cons ? ?));
  #HI #H lapply (HI (dist_dom_conservative … H)) *
  #Ha #Hb >Ha % //
  lapply H cases s #y #b
  whd in match (dist_dom ?);
  whd in match (match ? in Substitution with [_⇒?]);
  >(dist_dom_conservative … H) >if_then_true_else_false
  >domb_concat_distr
  #Hdd cut (domb_e y f = false)
  [ lapply Hdd cases domb_e cases domb_e normalize // ]
  normalize #HH >HH normalize @Hb
] qed.

  
lemma dist_dom_concat3:
 ∀e, f. dist_dom (concat e f)=true →
  ∀x. domb_e x f = true →
   domb_e x e = false.

#e #f #Hwn lapply (dist_dom_concat e f) >Hwn  #H' lapply (H' (refl …)) -H'
lapply Hwn
@(Environment_simple_ind2 …f) normalize
[ #_ #_ #j #abs destruct ] 
#f' * #y #b #H
whd in match (well_named_s ?);  whd in match (match ? in Substitution with [_⇒?]);
>domb_concat_distr #Hwn'
* #Ha lapply H -H
cut (dist_dom f' = true ∨ dist_dom f' = false) // * #Hddf >Hddf
[ 2: >if_monotone #_ #abs destruct ]
>if_then_true_else_false >Ha #H
cut (dist_dom (concat e f')= true ∨ dist_dom (concat e f')= false) // *
[ 2: #Htf lapply Hwn' >Htf >if_monotone #abs destruct ]
#Hyh lapply (H Hyh (conj … (refl …)(refl …))) -H #H
cut (domb_e y f' = true ∨ domb_e y f' = false) // * #Hdd >Hdd normalize
[ 1: #abs destruct] #_ lapply Hwn' >Hdd whd in match (orb ? ?);
>if_then_true_else_false >Hyh >if_then_true_else_false #Hju #x
cut (veqb x y = true ∨ veqb x y = false) // * #Hxy >Hxy normalize
[ elim (veqb_true_to_eq x y) #Heq #_ lapply (Heq Hxy) -Heq #Heq destruct
  #_ lapply Hju cases domb_e normalize //
| @H
] qed.
  
lemma four_dot_five_dot_three:
 (∀t,C,b,e,s. fresh_var_t t ≤ s → \fst (underline_pifTerm t s) = plug_c C 〈b, e〉 → 
  ∀x. (domb_cc x C ∧ fvb_b x b) = false).
  
#t #C #b #e cases C
  [ normalize //
  | #bb #ec #s #H cases ec #ee #y normalize #H' #x
    lapply (dis_dom t s x H)
    lapply (four_dot_one_dot_four) * #H414 #_
    lapply (H414 t s H)
    lapply H' cases underline_pifTerm * #bbb #eee #n -H' #H' destruct
    #Hwn
    cut (dist_dom (concat (Cons ee [y←b]) e)=true)
    [ lapply Hwn normalize cases dist_dom // >if_monotone #abs destruct ]
    -Hwn #Hdd lapply (dist_dom_concat3 … Hdd) #Hdd'
    normalize
    
    
    >fv_concat >domb_concat_distr
    whd in match (fvb_e ? ?); whd in match (domb_e ? (Cons ? ?));
    lapply (Hdd' x) normalize
    cut (veqb x y = true ∨ veqb x y = false) // * #Hxy >Hxy normalize
    [ elim (veqb_true_to_eq x y) #Heq #_ lapply (Heq Hxy) -Heq
      #Heq destruct cases domb_e
      [ #H lapply (H (refl …)) #abs destruct ]
       #_ >if_monotone >if_f >if_f >if_then_true_else_false >if_monotone >if_t
       cases fvb_b normalize // #H @H @refl
    | >if_then_true_else_false >if_then_true_else_false
      cases (domb_e x e)
      [ #Hyee >Hyee normalize //
      | normalize >if_then_true_else_false >if_then_true_else_false
        cases fvb_b
        [ >if_then_true_else_false >if_monotone >if_t #_ #H @H //
        | >if_monotone //
        ]
      ]
    ]
  ]
qed.