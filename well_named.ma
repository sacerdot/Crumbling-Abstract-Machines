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
        dist_dom (concat (push e1 [νm←b1]) (push e [ν(S m)←b]))=true .

#e1 #e #s #m #n #b #b1 #Hsn #Hnm
@(Environment_simple_ind2 … e)
[ #Hl1 #Hu1 #Hl2 #Hu2 #Hde #Hde1 whd in match (push Epsilon ?);
  whd in match (concat ? ?);
  >concat_e_epsilon
  whd in match (dist_dom ?);
  whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
  >dom_push >dist_dom_push
  whd in match (domb_e ? ?);
  whd in match (dist_dom ?);
  whd in match (dist_dom Epsilon);
  whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
  change with (neqb ? ?) in match (veqb ? ?);
  cut (∀n. neqb (S n) n=false) [ #n elim n //] #Hn >Hn -Hn >if_f
  cut (∀x:ℕ.n≤x → domb_e (νx) e1=false)
  [ #x lapply (Hu1 x) cases domb_e // #abs1 #abs2 @False_ind
    lapply (transitive_le … (abs1 (refl bool true)) abs2) /2/ ]
  #Hu1' >Hu1' >Hu1' normalize // @le_S assumption
| #e' * * #y #b #HI  #Hl1 #Hu1 #Hl2 #Hu2 #Hde #Hde1 
  whd in match (push (Cons ? ?) ?);
  whd in match (concat ? ?);
  whd in match (dist_dom ?);
  whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
  whd in match (dist_dom (Cons ? ?));
  whd in match (match ?  return λ_:Substitution.Variable with 
                  [subst (y:Variable)   (b0:Byte)⇒y]);
  >HI
  [ 6: @Hu1 | 7: @Hl1
  | 4: #x lapply (Hu2 x) whd in match (domb_e ? ?); cases veqb normalize
    [ #H #_ @H // | #H @H]
  | 5: #x lapply (Hl2 x) whd in match (domb_e ? ?); cases veqb normalize
    [ #H #_ @H // | #H @H ]
  | 2: @Hde1 | 3: lapply Hde normalize cases domb_e normalize [ #abs destruct] // 
  ]
  >domb_concat_distr >dom_push >dom_push >if_then_true_else_false
  whd in match (domb_e ? (Cons ? ?));
  whd in match (domb_e ? (Cons ? ?));
  whd in match (veqb ? ?);
  whd in match (veqb ? ?);
  cut (neqb y m=true ∨ neqb y m=false) // * #Hym >Hym normalize
  [ lapply (neqb_iff_eq y m) * #Heq #_ lapply (Heq  Hym) -Heq #Heq
    destruct @False_ind lapply (Hu2 m) normalize >Hym >if_t
    #abs @(le_Sn_n m) @abs //
  | cut (neqb y (S m)=true ∨ neqb y (S m)=false) // * #HySm >HySm normalize
    [ lapply (neqb_iff_eq y (S m)) * #Heq #_ lapply (Heq HySm) -Heq #Heq
      destruct @False_ind lapply (Hu2 (S m)) normalize >neqb_refl >if_t
      #abs cut (S m ≤ m) lapply (abs (refl …)) /2/
    ]
    normalize in Hde;
    lapply Hde cases domb_e normalize
    [ #abs destruct ]
    #_  lapply (Hl2 y) normalize >neqb_refl >if_t
    cut (n≤y → domb_e (νy) e1=false)
    [ 2: #H1 #H2 >H1 // @H2 //]
    lapply (Hu1 y)
    cases domb_e // #H1 #H2 @False_ind @(le_Sn_n y)
    @(transitive_le … (H1 (refl …)) H2)
  ]
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
      normalize //
      #Hdom1 #Hdom2
      >dist_dom_lemma
      [ //
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