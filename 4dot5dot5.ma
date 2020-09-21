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
(*
definition lvao_cc ≝ λcc.
 match cc with
 [ hole ⇒ True
 | crc b ec ⇒ match ec with
   [ envc e x ⇒ free_occ_t x (aux_read_back (read_back_b b) e) ≤1 ]
 ].
 *)
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
(*
lemma fresh_vua_lemma:
 (∀t, s. fresh_var_t t ≤ s → 
  fresh_vua_t t = fresh_vua (fst … (underline_pifTerm t s))) ∧
 (∀v, s. fresh_var_tv v ≤ s →
  fresh_vua_tv v = fresh_vua_v (fst … (overline v s))) .

@pifValueTerm_ind
[ #v #H #s normalize #HH lapply (H s) cases overline #vv #nn
  normalize -H #H >H //
  cases fresh_vua_v //
| 3: * #z #s normalize //
| 4: #t * #z #HI #s #H whd in match (overline ? ?);
  change with (max (S z) (fresh_var_t ?)≤s) in H;
  lapply (HI s (le_maxr … H)) -HI #HI whd in match (fresh_vua_tv ?);
  whd in match (match ? in Variable with [_⇒?]); >HI
  cases underline_pifTerm #c #n normalize //
| lapply (line_monotone_names) * #Hmono1 #Hmono2 #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s (le_maxl … H))
      lapply (Hmono2 v1 s)
      cases (overline v1 s) #vv #n #Hsn normalize
      lapply (H2 n (transitive_le … (le_maxr … H) Hsn))
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #ww #m normalize #Hnm
      #H2' #H1'
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if leb (abstr_bound_v vv) ? then ? else ?);
      change with (max ? ?) in match (if leb ? 0 then ? else ?); >max_O
      change with (max ? ?) in match (if ? then ? else ?) in H2';
      change with (max ? ?) in match (if ? then ? else ?) in H1';
      >max_O in H1'; >max_O in H2'; #H1' #H2' >H1' >H2' //
    | #u1 #u2 normalize #H1 #H2 #s
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s (le_maxl … H))
      lapply (Hmono1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then (fresh_var_t ?) else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hsn #H1'
      lapply (H2 n (transitive_le … (le_maxr … H) Hsn))
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #vv #m normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hnm #H2'
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if leb (abstr_bound_v vv) ? then ? else ?);
      change with (max ? ?) in match (if leb ? 0 then ? else ?);
      >abstr_bound_push whd in match (abstr_bound_e ?);
      whd in match (abstr_bound_s ?);
      change with (?= max ? ?) in H2';  >max_O in H2'; #H2'
      change with (max ? ?) in match (if ? then ? else ?) in H1';
      change with (max ? ?) in match (if ? then (abstr_bound_e ?) else ?) in H1';
      change with (max ? ?) in match (if ? then (abstr_bound_t u2) else ?);
      change with (max ? ?) in match (if ? then (abstr_bound_b b) else ?); 
      >H1' >H2' //
    ]
  | #u1 #u2 normalize #H1 #H2 #s
    lapply (H2 s)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hmono1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 normalize #H1
      lapply (H1 n) -H1 normalize
      lapply (Hmono2 v1 n)
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
        in match (if ? then max ? ? else ?); #Hnm
      #H1 #Hsn #H2 #Hm 
      change with (max ??) in match (if ? then ? else ?) in H1;
      >max_O in H1; #H1 >H1 [ 2: @(transitive_le … (le_maxl … Hm) Hsn) ]
      >H2 [ 2: @(le_maxr … Hm) ]
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if ? then abstr_bound_e ? else ?);
      change with (max ? ?) in match (if ? then 0 else ?); >max_O
      >concat_epsilon_e >abstr_bound_push
      change with (max ? ?) in match (abstr_bound_e (Cons ? ?));
      whd in match (abstr_bound_s ?); 
      change with (max ? ?) in match (if ? then (max (abstr_bound_e e1) ?) else abstr_bound_v vv);
      //
    | #r1 #r2 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hmono1 (appl r1 r2) n)
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
      #Hnm #H1' #Hsn #H2' #Hm
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      >H1' >H2' >abstr_bound_concat >abstr_bound_push >abstr_bound_push
      change with (max ? ?) in match (abstr_bound_e (Cons ? ?));
      change with (max ? ?) in match (abstr_bound_e (Cons e ?));
      whd in match (abstr_bound_s [(ν?)←b]);
      whd in match (abstr_bound_s [(ν?)←b1]);
      change with (max ? ?) in match (if ? then abstr_bound_e e else ?);
      change with (max ? ?) in match (if ? then abstr_bound_e e1 else ?);
      change with (max ? ?= max ? ?) //
    ]
  ]
] qed.


let rec abstr_bound_t t on t ≝
 match t with
 [ val_to_term v ⇒ abstr_bound_tv v
 | appl t1 t2 ⇒ max (abstr_bound_t t1) (abstr_bound_t t2)
 ]
 
and abstr_bound_tv v on v ≝
 match v with
 [ pvar x ⇒ 0
 | abstr z t ⇒ max (match z with [ variable n ⇒ n ]) (abstr_bound_t t)
 ] 
.

let rec abstr_bound c on c ≝
 match c with
 [ CCrumble b e ⇒ max (abstr_bound_b b) (abstr_bound_e e) ]
 
and abstr_bound_b b on b ≝ 
 match b with
 [ CValue v ⇒ abstr_bound_v v
 | AppValue v w ⇒ max (abstr_bound_v v) (abstr_bound_v w)
 ]
 
and abstr_bound_v v on v ≝
 match v with
 [ var x ⇒ 0
 | lambda x c ⇒ max (match x with [ variable n ⇒ n ]) (abstr_bound c)
 ]

and abstr_bound_e e on e ≝
 match e with
 [ Epsilon ⇒ 0
 | Cons e s ⇒ max (abstr_bound_e e) (abstr_bound_s s)
 ]

and abstr_bound_s s on s ≝
 match s with
 [ subst y b ⇒ abstr_bound_b b ]
.

lemma abstr_bound_push:
 ∀e, s. abstr_bound_e (push e s) = abstr_bound_e (Cons e s).
@Environment_simple_ind2 //
#e #s #HI #s1 whd in match (push ? ?); whd in match (abstr_bound_e ?); >HI
change with (max ? ?) in match (if ? then ? else ?);
change with (max ? ?) in match (abstr_bound_e ?);
change with (max ? ?) in match (abstr_bound_e (Cons (Cons e s) s1));
change with (max ? ?) in match (abstr_bound_e (Cons e s));
// qed.

lemma abstr_bound_concat:
 ∀f, e. abstr_bound_e (concat e f)= max (abstr_bound_e e) (abstr_bound_e f).
@Environment_simple_ind2
[ #e >concat_e_epsilon whd in match (abstr_bound_e Epsilon); >max_O @refl ]
#f #s #HI #s1 whd in match (concat ? ?);
whd in match (abstr_bound_e (Cons ? ?)); >HI
change with (max ? ?) in match (abstr_bound_e (Cons ? ?));
change with (max ? ? = max ? ?) //
qed.

lemma abstr_bound_lemma:
 (∀t, s. fresh_var_t t ≤ s → 
  abstr_bound_t t = abstr_bound (fst … (underline_pifTerm t s))) ∧
 (∀v, s. fresh_var_tv v ≤ s →
  abstr_bound_tv v = abstr_bound_v (fst … (overline v s))) .

@pifValueTerm_ind
[ #v #H #s normalize #HH lapply (H s) cases overline #vv #nn
  normalize -H #H >H //
  cases abstr_bound_v //
| 3: * #z #s normalize //
| 4: #t * #z #HI #s #H whd in match (overline ? ?);
  change with (max (S z) (fresh_var_t ?)≤s) in H;
  lapply (HI s (le_maxr … H)) -HI #HI whd in match (abstr_bound_tv ?);
  whd in match (match ? in Variable with [_⇒?]); >HI
  cases underline_pifTerm #c #n normalize //
| lapply (line_monotone_names) * #Hmono1 #Hmono2 #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s (le_maxl … H))
      lapply (Hmono2 v1 s)
      cases (overline v1 s) #vv #n #Hsn normalize
      lapply (H2 n (transitive_le … (le_maxr … H) Hsn))
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #ww #m normalize #Hnm
      #H2' #H1'
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if leb (abstr_bound_v vv) ? then ? else ?);
      change with (max ? ?) in match (if leb ? 0 then ? else ?); >max_O
      change with (max ? ?) in match (if ? then ? else ?) in H2';
      change with (max ? ?) in match (if ? then ? else ?) in H1';
      >max_O in H1'; >max_O in H2'; #H1' #H2' >H1' >H2' //
    | #u1 #u2 normalize #H1 #H2 #s
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s (le_maxl … H))
      lapply (Hmono1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then (fresh_var_t ?) else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hsn #H1'
      lapply (H2 n (transitive_le … (le_maxr … H) Hsn))
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #vv #m normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hnm #H2'
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if leb (abstr_bound_v vv) ? then ? else ?);
      change with (max ? ?) in match (if leb ? 0 then ? else ?);
      >abstr_bound_push whd in match (abstr_bound_e ?);
      whd in match (abstr_bound_s ?);
      change with (?= max ? ?) in H2';  >max_O in H2'; #H2'
      change with (max ? ?) in match (if ? then ? else ?) in H1';
      change with (max ? ?) in match (if ? then (abstr_bound_e ?) else ?) in H1';
      change with (max ? ?) in match (if ? then (abstr_bound_t u2) else ?);
      change with (max ? ?) in match (if ? then (abstr_bound_b b) else ?); 
      >H1' >H2' //
    ]
  | #u1 #u2 normalize #H1 #H2 #s
    lapply (H2 s)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hmono1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 normalize #H1
      lapply (H1 n) -H1 normalize
      lapply (Hmono2 v1 n)
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
        in match (if ? then max ? ? else ?); #Hnm
      #H1 #Hsn #H2 #Hm 
      change with (max ??) in match (if ? then ? else ?) in H1;
      >max_O in H1; #H1 >H1 [ 2: @(transitive_le … (le_maxl … Hm) Hsn) ]
      >H2 [ 2: @(le_maxr … Hm) ]
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max ? ?) in match (if ? then abstr_bound_e ? else ?);
      change with (max ? ?) in match (if ? then 0 else ?); >max_O
      >concat_epsilon_e >abstr_bound_push
      change with (max ? ?) in match (abstr_bound_e (Cons ? ?));
      whd in match (abstr_bound_s ?); 
      change with (max ? ?) in match (if ? then (max (abstr_bound_e e1) ?) else abstr_bound_v vv);
      //
    | #r1 #r2 #H1 normalize
      lapply (H1 n) normalize
      lapply (Hmono1 (appl r1 r2) n)
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
      #Hnm #H1' #Hsn #H2' #Hm
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      >H1' >H2' >abstr_bound_concat >abstr_bound_push >abstr_bound_push
      change with (max ? ?) in match (abstr_bound_e (Cons ? ?));
      change with (max ? ?) in match (abstr_bound_e (Cons e ?));
      whd in match (abstr_bound_s [(ν?)←b]);
      whd in match (abstr_bound_s [(ν?)←b1]);
      change with (max ? ?) in match (if ? then abstr_bound_e e else ?);
      change with (max ? ?) in match (if ? then abstr_bound_e e1 else ?);
      change with (max ? ?= max ? ?) //
    ]
  ]
] qed.

lemma no_occ:
 (∀t, s, x. fresh_var_t t ≤ s →
  fresh_var_t t ≤ x →
   x < s →
    inb (νx) (fst … (underline_pifTerm t s))=false ) ∧  
 (∀v, s, x. fresh_var_tv v ≤ s →
  fresh_var_tv v ≤ x →
   x < s →
    inb_v (νx) (fst … (overline v s))=false).
@pifValueTerm_ind
[ #p #H #s #x normalize #H1 #H2 #H3 lapply (H … H1 H2 H3) cases overline #vv #n
  normalize #HH >HH //
| 3: * #z #s #x normalize #H1 #H2 #H3
  cut (neqb x z = true ∨ neqb x z = false) // * #Hxz // elim (neqb_iff_eq x z)
  #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct @False_ind lapply H2
  @le_Sn_n
| 4: #t * #z #HI #s #x change with (max ? ?) in match (fresh_var_tv ?);
   #H1 #H2 #H3
  lapply (HI … (le_maxr … H1) (le_maxr … H2) H3) whd in match (overline ? ?);
  cases underline_pifTerm #c #n normalize #HH >HH >if_then_true_else_false
  cut (neqb x z = true ∨ neqb x z = false) // * #Hxz // elim (neqb_iff_eq x z)
  #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct @False_ind lapply (le_maxl … H2)
  @le_Sn_n
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
      change with (max ? ? ≤ ?) in HH;
      >if_then_true_else_false in H1'; #H1'
      >if_then_true_else_false in H2'; #H2'
      >H1' // [ 2: @(le_maxl … HH) ] >if_f
      >H2' // [ 2: @(le_maxr … HH) ] @(transitive_le … HHH Hsn)
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
      #Hline2 #Hnm #Hldom2 #Hbound2 >if_then_true_else_false #H2'
      change with (max (max ? ?) ?) in match (if ? then ? else ?);
      #HH #HHH >inb_push whd in match (inb_e ? ?); whd in match (inb_s ? ?);
      whd in match (veqb ? ?); >H2'
      [ 2: @(transitive_le … HHH Hsn)
      | 3: @((le_maxr … HH))
      | 4: @(transitive_le … (le_maxr … H) Hsn)
      ] >if_then_true_else_false
      lapply (orb_false … (H1' ? ? ?))
      [ @(le_maxl … H) | @(le_maxl … HH) | @HHH ]
      * #Ha #Hb >Ha >Hb >if_f >if_then_true_else_false
      cut (neqb x m = true ∨ neqb x m = false) // * #Hxm >Hxm // >if_t
      @False_ind elim (neqb_iff_eq x m) #Heq #_ lapply (Heq Hxm) -Heq #Heq
      destruct lapply (transitive_le … (transitive_le … HHH Hsn) Hnm)
      @le_Sn_n
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
      #H #HH >if_then_true_else_false in H1; #H1 >H1
      [ 2: @(transitive_le … HH Hsn)
      | 3: @((le_maxl … H))
      | 4: @(transitive_le … (le_maxl … Hm) Hsn)
      ] >if_f >concat_epsilon_e >inb_push
      whd in match (inb_e ? ?);
      whd in match (inb_s ? ?);
      whd in match (veqb ? ?);
      lapply (orb_false … (H2 ? ? ?))
      [ @(le_maxr … Hm)
      | @(le_maxr … H)
      | @HH
      ] * #Hb #He >Hb >He >if_f >if_then_true_else_false
      cut (neqb x m = true ∨ neqb x m = false) // * #Hxm >Hxm //
      @False_ind elim (neqb_iff_eq x m) #Heq #_
      lapply (Heq Hxm) #Heq destruct
      lapply (transitive_le … (transitive_le … HH Hsn) Hnm)
      @le_Sn_n
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
      #H #HH
      >inb_concat >inb_push >inb_push
      whd in match (inb_e ? ?);
      whd in match (inb_e ? (Cons ? [?←b]));
      whd in match (inb_s ? ?);
      whd in match (inb_s ? ([?←b]));
      whd in match (veqb ? ?);
      whd in match (veqb ? ?);
      lapply (orb_false … (H1' ? ? ?))
      [ @(transitive_le … (le_maxl … Hm) Hsn)
      | @(le_maxl … H)
      | @(transitive_le … HH Hsn)
      ] * #Hb #He >Hb >He >if_f  
      lapply (orb_false … (H2' ? ? ?))
      [ @((le_maxr … Hm))
      | @(le_maxr … H)
      | @HH
      ] * #Hb1 #He1 >Hb1 >He1 >if_f
      >if_then_true_else_false >if_then_true_else_false
      cut (neqb x m = true ∨ neqb x m = false) // * #Hxm >Hxm
      [ >if_monotone @False_ind elim (neqb_iff_eq x m) #Heq #_
        lapply (Heq Hxm) -Heq #Heq destruct
        lapply (transitive_le … (transitive_le … HH Hsn) Hnm)
        @le_Sn_n ] normalize
      >if_then_true_else_false
     cut (neqb x (S m) = true ∨ neqb x (S m) = false) // * #HxSm >HxSm
      [ >if_monotone @False_ind elim (neqb_iff_eq x (S m)) #Heq #_
        lapply (Heq HxSm) -Heq #Heq destruct
        lapply (le_S … (transitive_le … (transitive_le … HH Hsn) Hnm))
        @le_Sn_n ] //
    ]
  ]
] qed.

lemma nocc_nua: 
 (∀t, s, x. fresh_var_t t ≤ s →
   inb (νx) (fst … (underline_pifTerm t s))=false →
    nua (νx) (fst … (underline_pifTerm t s))=true) ∧  
 (∀v, s, x. fresh_var_tv v ≤ s →
   inb_v (νx) (fst … (overline v s))=false →
    nua_v (νx) (fst … (overline v s))=true).
@pifValueTerm_ind
[ #v #H #s #x normalize #HH lapply (H s x HH) cases overline #v #n normalize
  >if_then_true_else_false #HHH #HHHH lapply (HHH HHHH) //
| 3: #z #s #x #H1 normalize //
| 4: #t * #z #HH #s #x
  change with (max (S ?) ?) in match (fresh_var_tv ?);
  #Hm lapply (HH s x (le_maxr … Hm)) whd in match (overline  ? ?);
  cases underline_pifTerm #c #n normalize
  cut (inb (νx) c = true ∨ inb (νx) c = false) // * #Hinb
  [ >Hinb >if_monotone #_ #abs destruct ]
  >Hinb >if_then_true_else_false cut (fvb (νx) c = false)
  [ lapply (fv_to_in_crumble) * * * * #Hc #_ #_ #_ #_ lapply Hinb
    @(bool_impl_inv2) @Hc ]
  #HH >HH //
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  #t1 #t2 cases t2  
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s #x
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s x (le_maxl … H))
      lapply (Hmono2 v1 s)
      cases (overline v1 s) #vv #n #Hsn normalize
      lapply (H2 n x (transitive_le … (le_maxr … H) Hsn))
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #ww #m normalize #Hnm
      #H2' #H1' >if_then_true_else_false #HH
      lapply (orb_false … HH) * #Ha #Hb
      >if_then_true_else_false in H1'; #H1'
      >if_then_true_else_false in H2'; #H2' >H1' // >H2' //
    | #u1 #u2 normalize #H1 #H2 #s #x
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 s x)
      lapply (Hmono1 (appl u1 u2) s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n
      normalize
      change with (max (fresh_var_t ?) (fresh_var_t ?))
        in match (if ? then ? else ?);
      change with (max ? ?)
        in match (if ? then ? else (fresh_var_b ?));
      #Hsn #H1'
      lapply (H2 n x)
      lapply (Hmono2 v2 n)
      cases (overline v2 n) #vv #m normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hnm >if_then_true_else_false #H2'
      >inb_push >nua_push whd in match (inb_e (νx) (Cons ? ?));
      whd in match (nua_e (νx) (Cons ? ?));
      whd in match (inb_s (νx) ?);
      whd in match (nua_s (νx) ?);
      whd in match (veqb ? ?); cases neqb
      [ normalize #abs destruct ] normalize
      cut (inb_v (νx) vv = true ∨ inb_v (νx) vv = false) // * #Hvv >Hvv
      [ normalize #abs destruct ]
      cut (inb_e (νx) e = true ∨ inb_e (νx) e = false) // * #He >He
      [ normalize #abs destruct ]
      cut (inb_b (νx) b = true ∨ inb_b (νx) b = false) // * #Hb >Hb
      [ normalize #abs destruct ] normalize #_
      cut (nua_e (νx) e = true ∧ nua_b (νx) b = true)
      [ lapply (H1' (le_maxl … H)) >He >Hb normalize
        cases nua_e
        [ 2: >if_f #abs cut (false=true) [ @abs // ] #abs destruct ]
        >if_t cases nua_b
        [ #_ % //
        | #abs cut (false=true) [ @abs // ] #abs destruct ]
      ] * #He' #Hb' >He' >Hb' >H2' //
      @(transitive_le … (le_maxr … H) Hsn)
    ]
  | #u1 #u2 normalize #H1 #H2 #s #x
    lapply (H2 s x)
    change with (underline_pifTerm (appl u1 u2) s)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    lapply (Hmono1 (appl u1 u2) s)
    cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n
    lapply H1 -H1
    cases t1
    [ #v1 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hmono2 v1 n)
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
      #Hnm #H1 #Hsn #H2 #Hm #H
      lapply (H2 (le_maxr … Hm)) -H2 #H2
      lapply (H1 (transitive_le … (le_maxl … Hm) Hsn)) -H1 #H1
      >concat_epsilon_e >nua_push
      whd in match (nua_e ? ?);
      whd in match (nua_s ? ?);
      >if_then_true_else_false >H1
      [ 2: lapply H cases inb_v // ]
      >if_then_true_else_false @H2 lapply H
      >concat_epsilon_e >inb_push
      whd in match (inb_e ? ?);
      whd in match (inb_s ? ?);
      whd in match (veqb ? ?);
      cases neqb [ >if_monotone >if_t #abs destruct ]
      >if_then_true_else_false >if_f cases inb_v normalize [ #abs destruct ]
      cases inb_e normalize [ #abs destruct ] #H >H //
    | #r1 #r2 #H1 normalize
      lapply (H1 n x) normalize
      lapply (Hmono1 (appl r1 r2) n)
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
      #Hnm #H1' #Hsn #H2' #Hm
      lapply (H2' (le_maxr … Hm)) -H2' #H2'
      lapply (H1' (transitive_le … (le_maxl … Hm) Hsn)) -H1' #H1'
      >inb_concat >inb_push >inb_push
      whd in match (inb_e ? ?);
      whd in match (inb_e ? (Cons e ?));
      whd in match (inb_s ? ?);
      whd in match (inb_s ? ?);
      whd in match (veqb ? ?);
      whd in match (veqb ? ?);
      >nua_concat >nua_push >nua_push
      whd in match (nua_e ? (Cons ? ?));
      whd in match (nua_e ? (Cons e ?));
      whd in match (nua_s ? ?);
      whd in match (nua_s ? [?←b]);
      >if_then_true_else_false
      cases neqb normalize [ #abs destruct ]
      cases neqb normalize [ #abs destruct ]
      cut ((if inb_e (νx) e1 then true else inb_b (νx) b1) = true ∨
          if inb_e (νx) e1 then true else inb_b (νx) b1 = false ) // * #Hif
      >Hif normalize [ #abs destruct ] #Hif2
      >H1' [ 2: lapply Hif2 cases inb_e normalize [ #abs destruct ] #H >H // ]
      >H2' // lapply Hif cases inb_e normalize [ #abs destruct ] #H >H //
    ]
  ]
] qed.
*)
 
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
 
(*
lemma delirium_lemma1: ∀e, h, f, g, s, t, u.
 1 ≤ e_len g →  
 e_len g ≤ e_len e → (concat (push e s) (push f t)=concat (Cons g u) h) → 
  (∃d, p. g = push d s ∧ e = concat (Cons d u) p ∧ h = (concat (Cons p t) f)).

@(Environment_double_ind2)
[ #f #h #s #t #u normalize #abs #absb @False_ind lapply (transitive_le …abs absb) @le_Sn_n
| #hh #ss #f #g #s #t #u #H1 #H2 >concat_e_epsilon #H lapply (e_len_lemma … H)
  >concat_len >push_len >push_len normalize lapply H2
  whd in match (e_len (Cons ? ?)); -H2 #H2 #HH cut (e_len g = S (e_len hh+S (e_len f)))
   [ /2/ ] -HH #HH lapply H2 >HH #abs @False_ind lapply abs
| #gg #ss #f #h #s #t #u normalize #abs #absb @False_ind lapply (transitive_le …abs absb) @le_Sn_n
| #g #e #gs #es #HI #f #h #s #t #u normalize
*)

lemma delirium_lemma:
 ∀e, f, g, h, s, t, u. (concat (push e s) (push f t)=concat (Cons g u) h) →
  (g=Epsilon ∧ s=u ∧ h = concat e (push f t)) ∨
   (∃d, p. g = push d s ∧ e = concat (Cons d u) p ∧ h = (concat (Cons p t) f)) ∨
(*    (∃d. g = push d s ∧ e = Cons d u ∧ h = concat t f) ∨ *)
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
(* 
lemma tc_term_rb:
∀v, x. no_hole (hole_subst (read_back_v v) x) →
 tc_term (hole_subst (read_back_v v) x).
 
*
[ #x #z normalize cases veqb normalize //
| #z * #b #e #x normalize cases veqb normalize //
] qed.

lemma not_under_abstr:
 (∀t, x, s.
  fresh_var_t t ≤ s →
   domb x (fst … (underline_pifTerm t s)) = true →
    nua x (fst … (underline_pifTerm t s)) = true) ∧
 (∀v:pifValue. True).
@pifValueTerm_ind
[ #v #_ #x #s whd in match (underline_pifTerm ? ?);
  cases overline #vv #n normalize #_ #abs destruct
| 3: //
| 4: //
| lapply (line_monotone_names) * #Hmono1 #Hmono2
  lapply (line_names) * #Hline1 #Hline2
  lapply (line_dom) #Hldom
  lapply (env_bound_lemma) #Hbound
  lapply no_occ * #nocct #noccv #t1 #t2 cases t2  
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #x #s
      change with (max (fresh_var_tv ?) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 x s (le_maxl … H))
      lapply (Hmono2 v1 s)
      lapply (noccv v1 s)
      cases (overline v1 s) #vv #n #Hfvv1 #Hsn normalize
      lapply (H2 x n (transitive_le … (le_maxr … H) Hsn))
      lapply (Hmono2 v2 n)
      lapply (noccv v2 n)
      cases (overline v2 n) #ww #m #Hfvv2 normalize #Hnm
      #H2' #H1' #abs destruct
    | #u1 #u2 normalize #H1 #H2 #x #s
      change with (max (max (fresh_var_t ?) (fresh_var_t ?)) (fresh_var_tv ?))
        in match (if ? then ? else ?); #H
      lapply (H1 x s)
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
      lapply (H2 x n)
      lapply (Hbound (val_to_term v2) n)
      lapply (Hldom (val_to_term v2) n) normalize
      lapply (Hmono2 v2 n)
      lapply (Hline2 v2 n)
      lapply (noccv v2 n x)
      cases (overline v2 n) #vv #m #Hfvv2 normalize
      change with (fresh_var_tv ?) 
        in match (pi1 nat ? ?);
      #Hline2 #Hnm #Hldom2 #Hbound2 #H2' #Hdom
      destruct >dom_push in Hdom; whd in match (domb_e ? ?);
      cut (veqb x (νm)=true ∨ veqb x (νm)=false) // * #Hxm
      [ elim (veqb_true_to_eq … x νm) #Heq #_ lapply (Heq Hxm) -Heq #Heq
        destruct normalize >nua_push whd in match (nua_e ? ?);
        whd in match (nua_s ? ?); #_ lapply inb_to_nua_crumble * * * *
        #_ #Hnb #Hne #Hnv #_
        lapply fresh_var_to_in_crumble * * * * #_ #Hb #He #Hv #_
         >Hnv
        [ 2: @Hv @Hline2 @(transitive_le … (le_maxr … H) Hsn) ]
        >Hnb
        [ 2: @Hb @(transitive_le … (le_maxl … (Hline1 … (le_maxl … H))) Hnm) ]
        >if_then_true_else_false >if_then_true_else_false @Hne
        @He @(transitive_le … (le_maxr … (Hline1 … (le_maxl … H))) Hnm)
      ]
      >Hxm >if_f #Hdome >nua_push whd in match (nua_e ? ?);
      whd in match (nua_s ? ?);
      cut (nua_v x vv = true) [ 2: #HH >HH >if_then_true_else_false @H1' //
      @(le_maxl … H) ]u
      
       
      
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

corollary c111: ∀C, c. 
 (∀x. (fvb_cc x C ∧ domb x c) = false) → 
  well_named (plug_c C c) = true → 
   read_back (plug_c C c) = plug_t (cc_read_back C) (read_back c).
@CrumbleContext_ind
[ * #b #e #H normalize //
| #b * #e #y * #bb
  @Environment_simple_ind2
  [ #_ #H normalize whd in match (concat (Cons ? ?) Epsilon);
    change with ((read_back_b bb)) in match (aux_read_back (read_back_b bb) Epsilon);
    change with (pif_subst (aux_read_back (read_back_b b) e) (psubst y (read_back_b bb)))
      in match (aux_read_back (read_back_b b) (Cons e [y ←bb]));
    lapply H -H
    whd in match (plug_c ? ?);
    whd in match (plug_e ? ?);
    #H
    whd in match (well_named ?); @pif_subst_plug
*)
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
*)
lemma contextual_decoding: (∀t, C, c, s.
 fresh_var_t t ≤ s →
  fst … (underline_pifTerm t s) = plug_c C c →
   lvao_cc C).

#t * [ normalize // ] #b * #e #y * #d #f #s #H1
(* lapply dom_var_occ * #Hdv #_ lapply (Hdv t s y) -Hdv *)
cases underline_pifTerm * #b' #e' #n normalize
#H destruct

 
(*
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