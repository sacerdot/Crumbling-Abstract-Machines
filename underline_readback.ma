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

include "crumbles.ma".
include "basics/types.ma".
include "libnat.ma".
include "variables.ma".
include "utils.ma".
include "size.ma".
include "alternative_pif_subst.ma".


notation "[ term 19 v ← term 19 b ]" non associative with precedence 90 for @{ 'substitution $v $b }.
interpretation "Substitution" 'substitution v b =(subst v b).

(*notation "〈 b break, e 〉" non associative with precedence 90 for @{ 'ccrumble $b $e }.
*)
interpretation "Crumble creation" 'pair b e =(CCrumble b e).

notation "𝛌 x . y" right associative with precedence 40 for @{ 'lambda $x $y}.
interpretation "Abstraction" 'lambda x y = (lambda x y ).

notation "ν x" non associative with precedence 90 for @{ 'variable $x}.
interpretation "Variable contruction" 'variable x = (variable x).

notation "hvbox(c @ e)" with precedence 35 for @{ 'at $c $e }.
interpretation "@ operation" 'at c e =(at c e).

(* deve restituire una coppia 〈crumble, numero di variabili già inserite〉 per usare il parametro destro sommato al numero di variabili presenti nel termine all'inizio per dare sempre una variabile fresca*)
(*
let rec underline_pifTerm (t: pifTerm) (s: nat): Crumble × nat≝
 match t with
 [ val_to_term v ⇒ match overline v s with
   [ mk_Prod vv n ⇒  mk_Prod Crumble nat 〈(CValue vv), Epsilon 〉 n]
 | appl t1 t2 ⇒ match t2 with
   [ val_to_term v2 ⇒ match t1 with
     [ val_to_term v1 ⇒ match overline v1 s with
       [ mk_Prod vv n ⇒ match overline v2 (s+n) with
         [ mk_Prod ww m ⇒ mk_Prod Crumble nat 〈AppValue (vv) (ww), Epsilon〉 (m+n) ]
       ]
     | appl u1 u2 ⇒ match underline_pifTerm t1 s with
       [ mk_Prod c n ⇒ match c with
         [ CCrumble b e ⇒ match overline v2 (s+n) with
           [ mk_Prod vv m ⇒ mk_Prod Crumble nat 〈AppValue (var ν(s+n+m)) (vv), push e [(ν(s+n+m)) ← b]〉 (S (s+n+m))]
         ]
       ]
     ]
   | appl u1 u2 ⇒ match underline_pifTerm t2 s with
     [ mk_Prod c n ⇒ match c with
       [ CCrumble b1 e1 ⇒ match t1 with
         [ val_to_term v1 ⇒ match overline v1 (s+n) with
           [ mk_Prod vv m ⇒  mk_Prod Crumble nat (at 〈AppValue (vv) (var ν(s+n+m)), Epsilon〉 (push e1 [ν(s+n+m)←b1])) (S n + m)]
         | appl u1 u2 ⇒ match underline_pifTerm t1 (s+n) with
          [ mk_Prod c1 n1 ⇒ match c1 with
            [ CCrumble b e ⇒ mk_Prod Crumble nat 〈AppValue (var (ν(s+n+n1))) (var (ν(S(s+n+n1)))), concat (push e1 [ν(s+n+n1) ← b1]) (push e [ν(S(s+n+n1)) ← b])〉 (S (S (s + n + n1)))]
          ]
         ]
       ]
     ]
   ]
 ]

and

overline (x:pifValue) (s: nat): Value × nat≝
 match x with
 [ pvar v ⇒ mk_Prod Value nat (var v) O
 | abstr v t ⇒ match underline_pifTerm t s with
   [ mk_Prod c n ⇒ mk_Prod Value nat (lambda (v) (c)) n ]
 ]
 .
 *)

let rec underline_pifTerm (t: pifTerm) (s: nat): Crumble × nat≝
 match t with
 [ val_to_term v ⇒ match overline v s with
   [ mk_Prod vv n ⇒  mk_Prod Crumble nat 〈(CValue vv), Epsilon 〉 n]
 | appl t1 t2 ⇒ match t2 with
   [ val_to_term v2 ⇒ match t1 with
     [ val_to_term v1 ⇒ match overline v1 s with
       [ mk_Prod vv n ⇒ match overline v2 n with
         [ mk_Prod ww m ⇒ mk_Prod Crumble nat 〈AppValue (vv) (ww), Epsilon〉 m ]
       ]
     | appl u1 u2 ⇒ match underline_pifTerm t1 s with
       [ mk_Prod c n ⇒ match c with
         [ CCrumble b e ⇒ match overline v2 n with
           [ mk_Prod vv m ⇒ mk_Prod Crumble nat 〈AppValue (var ν(m)) (vv), push e [(ν(m)) ← b]〉 (S m)]
         ]
       ]
     ]
   | appl u1 u2 ⇒ match underline_pifTerm t2 s with
     [ mk_Prod c n ⇒ match c with
       [ CCrumble b1 e1 ⇒ match t1 with
         [ val_to_term v1 ⇒ match overline v1 n with
           [ mk_Prod vv m ⇒  mk_Prod Crumble nat (at 〈AppValue (vv) (var (νm)), Epsilon〉 (push e1 [νm←b1])) (S m)]
         | appl u1 u2 ⇒ match underline_pifTerm t1 n with
          [ mk_Prod c1 n1 ⇒ match c1 with
            [ CCrumble b e ⇒ mk_Prod Crumble nat 〈AppValue (var (ν(S(n1)))) (var (νn1)), concat (push e1 [νn1 ← b1]) (push e [ν(S(n1)) ← b])〉 (S (S (n1)))]
          ]
         ]
       ]
     ]
   ]
 ]

and

overline (x:pifValue) (s: nat): Value × nat≝
 match x with
 [ pvar v ⇒ mk_Prod Value nat (var v) s
 | abstr v t ⇒ match underline_pifTerm t s with
   [ mk_Prod c n ⇒ mk_Prod Value nat (lambda (v) (c)) (max (S match v with [variable nx ⇒ nx]) n)  ]
 ]
 .
 
lemma line_monotone_names:
 (∀t.∀s.  snd … (underline_pifTerm t s) ≥ s) ∧
  (∀v.∀s. snd … (overline v s) ≥ s).
  
@pifValueTerm_ind
[ #v #HI #s lapply (HI s) normalize cases (overline v s) //
| #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s lapply (H1 s) cases (overline v1 s) #vv #n
      normalize lapply (H2 n) cases (overline v2 n) #ww #m normalize
      #H2 #H1 @(transitive_le … H1 H2)
    | #u1 #u2 normalize #H1 #H2 #s lapply (H1 s) 
      change with (underline_pifTerm (appl u1 u2) ?)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n normalize -H1 #H1
      lapply (H2 n) cases (overline v2 n) #ww #m normalize #H2 @le_S
      @(transitive_le … H1 H2)
    ]
    | #u1 #u2 #Hu1 #Hu2 #s lapply (Hu2 s) normalize
      change with (underline_pifTerm (appl u1 u2) ?)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n -Hu2 #Hu2
      lapply Hu1 cases t1 normalize
      [ #v1 -Hu1 #Hu1 lapply (Hu1 n) cases (overline v1 n) #vv #m normalize #Hn
        @le_S @(transitive_le … Hu2 Hn)
      | #u1 #u2 #Hu2 lapply (Hu2 n)
        change with (underline_pifTerm (appl u1 u2) n) 
          in match ( match u2 in pifTerm with [_⇒ ?]);
        cases (underline_pifTerm (appl u1 u2) n) * #b #e #m normalize
        #Hm @le_S @le_S -Hu2 @(transitive_le … Hu2 Hm)
      ]
    ]  
| #x #s normalize //
| #t * #x #H #s lapply (H s) normalize cases ((underline_pifTerm t s)) #c #n
  normalize
  change with (leb (S x) n) in match (match n in nat with [_⇒ ?]);
  cut (leb (S x) n = true ∨ leb (S x) n= false)  // * #Hleb >Hleb // >if_f
  lapply (leb_false_to_not_le … Hleb) #Hnle lapply (not_le_to_lt … Hnle)
  -Hnle #H1 #H2 lapply (lt_to_le … (le_to_lt_to_lt … H2 H1)) // 
] qed.
 
lemma line_names:
 (∀t.∀s. s ≥ fresh_var_t t → snd … (underline_pifTerm t s) ≥ fresh_var (fst … (underline_pifTerm t s))) ∧
  (∀v.∀s. s ≥ fresh_var_tv v → snd … (overline v s) ≥ fresh_var_v (fst … (overline v s))).

@pifValueTerm_ind
[ #v #HI #s normalize #H lapply (HI s) -HI #HI lapply (HI H) -HI cases (overline v s)
  #vv #n normalize #Hn cases (leb) //
| 3: * #x #s normalize //
| 4: #t * #x #H #s normalize
  change with (max (S x) (fresh_var_t t)) in match (if match pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t→S x0≤n) (fresh_var_t_Sig t)
         in nat
         return λ_:ℕ.bool
         with 
        [O⇒false|S (q:ℕ)⇒leb x q] 
   then pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t→S x0≤n) (fresh_var_t_Sig t) 
   else S x );
  #Hs change with (if leb ? ? then ? else ?) in match (max ? ?) in Hs;
  cut (leb (S x) (fresh_var_t t)=true ∨ leb (S x) (fresh_var_t t)=false) // *
  #Hleb >Hleb in Hs; #Hs
  [ >if_t in Hs; #Hs lapply (H … Hs)
   lapply (line_monotone_names) * #Hmonotone #_ lapply (Hmonotone t s)
   cases (underline_pifTerm)
    #c #n -Hmonotone #Hmonotone normalize
    change with (leb (S ?) ?) in match (match ? in nat return λ_:ℕ.bool with 
         [O⇒false|S (q:ℕ)⇒leb x q] );
        change with (leb (S ?) ?) in match (match n in nat return λ_:ℕ.bool with 
         [O⇒false|S (q:ℕ)⇒leb x q] );
    change with (max ? ?) in match (if leb (S ?) ? then ? else ?);
    change with (max ? ?) in match (if leb (S x) n then n else ?);
    lapply (leb_true_to_le …Hleb) -Hleb #Hle normalize in Hmonotone;
    lapply (transitive_le …Hs Hmonotone) #Htrans
    lapply (transitive_le … Hle Htrans) -Hle #Hle
    lapply (le_to_leb_true … Hle) -Hle #Hleb >Hleb
    #HH @(to_max) // >max_comm @le_le_max assumption
  | >if_f in Hs; #Hs
    lapply(leb_false_to_not_le … Hleb) #Hnle
    lapply (not_le_to_lt … Hnle) -Hnle #Hlt
    lapply (lt_to_le … Hlt) -Hlt #Hfvt
    lapply (transitive_le … Hfvt Hs) -Hs -Hfvt
    #Hle lapply (H … Hle)  
    lapply (line_monotone_names) * #Hmonotone #_ lapply (Hmonotone t (s))
    cases (underline_pifTerm) #c #n -Hmonotone #Hmonotone normalize
    change with (leb (S ?) ?) in match (match n in nat return λ_:ℕ.bool with 
         [O⇒false|S (q:ℕ)⇒leb x q] );
    change with (leb (S ?) ?) in match (match fresh_var ? in nat return λ_:ℕ.bool with 
         [O⇒false|S (q:ℕ)⇒leb x q] );
    change with (max ? ?) in match (if leb ? ? then ? else ?);
    change with (max ? ?) in match (if leb (S x) n then ? else ?);
    #HH @to_max // >max_comm @le_le_max assumption
  ]
| #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s lapply (H1 s)
      lapply line_monotone_names * #_ #Hmono
      lapply (Hmono v1 s)
      cases (overline v1 s) #vv #n #Hns normalize
      lapply (H2 n) lapply (Hmono v2 n)
      cases (overline v2 n) #ww #m #Hmn normalize
      change with (fresh_var_tv ?) 
        in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_v (νx) v1→S x≤n0) (fresh_var_tv_Sig v1));
      change with (fresh_var_tv ?) 
        in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_v (νx) v2→S x≤n0) (fresh_var_tv_Sig v2));
      change with (max ? ?) in match (if leb ? ? then ? else ?);
      change with (max ? ?) in match (if leb ? (fresh_var_tv ?) then ? else ?);
      change with (max ? ?) in match (if leb ? (fresh_var_v ?) then ? else ?);
      change with (max ? ?) in match (if leb (max ? ?) 0 then 0 else ?);
      change with (max ? ?) in match (if leb (fresh_var_v vv) O then O else ?);
      >max_O >max_O >max_O #H2 #H1 #Hb lapply (le_maxl …Hb) lapply (le_maxr …Hb)
      #Hv2 #Hv1 lapply (H2 (transitive_le … Hv2 Hns)) #Hww
      lapply (transitive_le …(H1 Hv1) Hmn) #Hvv
      @to_max //      
    | #u1 #u2 normalize #H1 #H2 #s lapply (H1 s) 
      change with (underline_pifTerm (appl u1 u2) ?) 
        in match ( match u2 in pifTerm with [_⇒ ?]);
      lapply (line_monotone_names) * #Hmono1 #Hmono2 lapply (Hmono1 (appl u1 u2) s)
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n normalize -H1 #Hsn 
      lapply (Hmono2 v2 n) 
      lapply (H2 n) cases (overline v2 n) #ww #m normalize
      change with (fresh_var_t ?)
        in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) u1→S x≤n0) (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) u2→S x≤n0) (fresh_var_t_Sig u2));
      change with (fresh_var_tv ?)
        in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_v (νx) v2→S x≤n0) (fresh_var_tv_Sig v2));
      change with (max ? ?) in match (if ? then ? else ? ); >max_O #H1 #Hnm
      change with (max ? ?) in match (if ? then ? else ? );
      change with (max ? ?) in match (if leb (fresh_var_b ?) ? then ? else ?);
      change with (max ? ?) in match (if leb (max ? ?)? then ? else ?); #H2 #H
      change with (leb (S ?) ?) in match (match ? in nat with [_ ⇒ ?]);
      change with (max ? ?) in match (if ? then ? else ?);
      change with (max (?) ?) in match ((if leb (S m) (fresh_var_v ww) then fresh_var_v ww else S m ));
      <(fresh_var_push e [νm ← b])
      whd in match (fresh_var_e ?) in ⊢%;
      change with (max ? ?) in match (if ? then ? else fresh_var_e e);
      @to_max @to_max
      [ //
      | @(le_S …(H1 (transitive_le … (le_maxr … H ) Hsn)))
      | @(le_S …(le_maxr …(transitive_le … (H2 (le_maxl … H)) Hnm)))
      | change with (max (S m) ?) in match (fresh_var_s ?); @to_max
        [ //
        | @(le_S … (le_maxl … (transitive_le … (H2 (le_maxl … H)) Hnm)))
        ]
      ]
    ]
  | #u1 #u2 #Hu1 #Hu2 #s lapply (Hu2 s) normalize
      change with (underline_pifTerm (appl u1 u2) ?)
        in match ( match u2 in pifTerm with [_⇒ ?]);
      lapply (line_monotone_names) * #Hmono1 #Hmono2 lapply (Hmono1 (appl u1 u2) s)
      cases (underline_pifTerm (appl u1 u2) s) * #b1 #e1 #n #Hsn
      lapply Hu1 cases t1 normalize
      [ #v1 -Hu1 #Hu1 lapply (Hu1 n)
        lapply (Hmono2 v1 n)  cases (overline v1 n) #vv #m normalize #Hnm
        change with (fresh_var_t ?)
        in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) u1→S x≤n0) (fresh_var_t_Sig u1));
        change with (fresh_var_t ?)
          in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) u2→S x≤n0) (fresh_var_t_Sig u2));
        change with (fresh_var_tv ?)
          in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_v (νx) v1→S x≤n0) (fresh_var_tv_Sig v1));
        change with (max ? ?) in match (if ? then ? else ? ); >max_O #H1
        change with (max ? ?) in match (if ? then ? else ? );
        change with (max ? ?) in match (if leb (fresh_var_b ?) ? then ? else ?); #H2
        change with (max ? ?) in match (if leb (max ? ?)? then ? else ?);
        change with (max ? ?) in match (if leb (fresh_var_tv ?) ? then ? else ?);
        change with (max ? ?) in match (if leb (fresh_var_v ?) ? then ? else ?); #H
        >concat_epsilon_e <fresh_var_push
        change with (max ? ?) in match (fresh_var_e ?);
        change with (max ? ?) in match (fresh_var_s ?);
        @to_max
        [ @to_max
          [ @(le_S …(H1 (transitive_le … (le_maxl … H ) Hsn)))
          | //
          ]
        | @to_max
          [ @(le_S …(le_maxr …(transitive_le … (H2 (le_maxr … H)) Hnm)))
          | @to_max // @(le_S …(le_maxl …(transitive_le … (H2 (le_maxr … H)) Hnm)))
          ]
        ]
      | #t1 #t2 #Ht2 lapply (Ht2 n)
        change with (underline_pifTerm (appl t1 t2) n)
          in match ( match t2 in pifTerm with [_⇒ ?]); 
        lapply (line_monotone_names) * #Hmono1 #Hmono2 lapply (Hmono1 (appl t1 t2) n)
        cases (underline_pifTerm (appl t1 t2) n) * #b #e #m normalize #Hnm
        change with (fresh_var_t ?)
          in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) u1→S x≤n0) (fresh_var_t_Sig u1));
        change with (fresh_var_t ?)
          in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) u2→S x≤n0) (fresh_var_t_Sig u2));
        change with (fresh_var_t ?)
          in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) t1→S x≤n0) (fresh_var_t_Sig t1));
        change with (fresh_var_t ?)
          in match (pi1 ℕ (λn0:ℕ.∀x:ℕ.1≤free_occ_t (νx) t2→S x≤n0) (fresh_var_t_Sig t2));
        change with (max ? ?) in match (if  ? then ?  else ?);
        change with (max ? ?) in match (if leb (fresh_var_b b) (fresh_var_e e) 
                                        then ? else ?); #H1
        change with (max (fresh_var_t ?) (fresh_var_t ?)) in match (if  ? then ?  else ?);
        change with (max ? ?) in match (if leb (fresh_var_b b1) ? 
                                        then ? else ?); #H2
        change with (max ? ?) in match (if ? then ? else ?) in ⊢ (% → ?);
        #H
        change with (max (S (S m)) (S m)) in match (if match m in nat with [_ ⇒ ?] 
            then S m 
            else S (S m));
        change with (max ? ?)
          in match (if leb (max (S (S m)) (S m))
                    (fresh_var_e (concat (push e1 [νm←b1]) (push e [ν(S m)←b]))) 
                    then fresh_var_e (concat (push e1 [νm←b1]) (push e [ν(S m)←b])) 
                    else max (S (S m)) (S m));
        >fresh_var_concat <fresh_var_push <fresh_var_push 
        whd in match (fresh_var_e (Cons e1 [νm←b1]));
        whd in match (fresh_var_s ?);
        whd in match (fresh_var_e (Cons e [ν(S m)←b]));
        whd in match (fresh_var_s ?);
        
        change with (max ? ?) in match (if leb (S m) ? then ? else ?);
        change with (max ? ?) in match (if leb (S m) (fresh_var_b ?) then ? else ?);
        change with (max ? ?) in match (if leb (fresh_var_e e1) ? then ? else ?);
        change with (max ? ?) in match (if leb (fresh_var_e e) ? then ? else ?);
        change with (max ? ?)
          in match (if leb (S (S m)) (fresh_var_b b) then fresh_var_b b else S (S m)); 
        @to_max
        [ @to_max //
        | @to_max
          [ @to_max
            [ @(le_S …(le_S … (transitive_le … (le_maxr …(H2 (le_maxr … H))) Hnm)))
            | @to_max
              [ //
              | @(le_S …(le_S … (transitive_le … (le_maxl … (H2 (le_maxr … H))) Hnm)))
              ]
            ]
          | @to_max
            [ @(le_S …(le_S … (le_maxr … (H1 (transitive_le … (le_maxl … H) Hsn)))))
            | @to_max //
              @(le_S …(le_S … (le_maxl … (H1 (transitive_le … (le_maxl … H) Hsn)))))
            ]
          ]
        ]
      ]
    ]
] qed.

definition interval_dom ≝  λe, b. ∀x. domb_e (νx) e =true → b ≤ x.

lemma interval_lemma:  ∀x, e, s. interval_dom (Cons e s) x → interval_dom e x.
#x #e #s  @(Environment_simple_ind2 … e)
[ #H normalize #x #abs destruct
| cases s #y #t normalize #e' #s' elim y #ny normalize #H #H' #x0 lapply (H' x0)
  cases (neqb x0 ny)
  [ normalize #Htot #_ @Htot //
  | normalize #Htot @Htot
  ]
]
qed.

lemma line_dom: 
 (∀t. ∀s. (interval_dom match (fst … (underline_pifTerm t s)) with [CCrumble c e ⇒ e] s)).

#t elim t

[ @(λv. True)
| #v #_ #s normalize cases (overline v s) #vv #n #x normalize #abs destruct
| lapply (line_monotone_names) * #Hmono1 #Hmono2 #t1 #t2 #H1 #H2 #s lapply H2
  cases (t2)
  [ #v2 lapply H1 cases t1
    [ #v1 normalize cases (overline v1 s) #vv #n normalize 
      cases (overline v2 n) #ww #m
      normalize #_ #_ #x #abs destruct
    | #u1 #u2 normalize #H1 #H2 lapply (H1 s)
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);     lapply (Hmono1 (appl u1 u2) s)
     cases (underline_pifTerm (appl u1 u2) s) *
     #b #e #n normalize #Hsn
     lapply (H2 n)
     lapply (Hmono2 v2 n)
     cases (overline v2 (n)) #vv #m normalize #Hnm
     -H1 -H2 #H2' #H1'
     #x >dom_push normalize
     lapply (H1' x)
     cut (neqb x m=true ∨ neqb x m=false) // * #Htf >Htf normalize
     [ lapply (neqb_iff_eq x m) * #Heq #_ lapply(Heq Htf) -Heq #Heq
       destruct #_ #_ @(transitive_le … Hsn Hnm)
     | #Hdomb #HH @(Hdomb HH)
     ] 
   ]
 | #u1 #u2 #H2' lapply (H2' s) normalize
      change with (underline_pifTerm (appl u1 u2) s)
        in match ( match u2 in pifTerm with [_⇒ ?]);
   lapply (Hmono1 (appl u1 u2) s)
   cases (underline_pifTerm (appl u1 u2) s)
   * #b1 #e1 #n normalize #Hsn
   lapply (H1 n) cases t1
   [ #v1 normalize lapply (Hmono2 v1 n)
     cases (overline v1 n)
     #vv #m normalize #Hnm #_
     #H2' #x lapply (H2' x) normalize
     cut (neqb x m=true ∨ neqb x m=false) // * #Htf
     [ lapply (neqb_iff_eq x m) * #Heq #_
       lapply (Heq Htf) -Heq #Heq destruct >concat_epsilon_e >dom_push
       normalize
       >neqb_refl normalize #_ #_ @(transitive_le … Hsn Hnm)
     | >concat_epsilon_e >dom_push #HH
       normalize >Htf >if_f @H2'
     ]
   | #u1 #u2 lapply (Hmono1 (appl u1 u2) n)
     cases (underline_pifTerm (appl u1 u2) n)
     * #b #e #n1 normalize #Hnn1
     #H1' #H2'' #x lapply (H2'' x) lapply (H1' x) -H2'' -H1'
     #H1' #H2'' normalize >domb_concat_distr >dom_push >dom_push
     normalize cut (neqb x n1=true ∨ neqb x n1=false) // * #Htf
     [ lapply (neqb_iff_eq x n1) * #Heq #_
       lapply (Heq Htf) -Heq #Heq destruct >Htf #_ 
       @(transitive_le … Hsn Hnn1)
     | cut (neqb x (S n1)=true ∨ neqb x (S n1)=false) // *
       #Htf'
       [ lapply (neqb_iff_eq x (S n1)) * #Heq #_
         lapply (Heq Htf') -Heq #Heq destruct #_
         @le_S @(transitive_le … Hsn Hnn1)
       | >Htf >Htf' normalize -Htf -Htf'
         cut (domb_e (νx) e1 = true ∨ domb_e (νx) e1 =false) // *
         #Htf >Htf
         [ #_ @(H2'' Htf)
         | normalize #H @(transitive_le … Hsn (H1' H))
         ]
       ]
     ]
   ]
 ]

|  #_ //
|  #t #x #_ //
] qed.

let rec c_len_e e on e ≝ match e with [Epsilon ⇒ O | Cons e s ⇒ 1 + c_len_e e].

let rec c_len c on c ≝
 match c with
 [ CCrumble b e ⇒ c_len_e e].

let rec e_pop e on e ≝
 match e with
 [ Epsilon ⇒ e
 | Cons e s ⇒ e
 ]
 .

let rec fv_pt x t on t≝
 match t with
 [ val_to_term v ⇒ fv_pv x v
 | appl t1 t2 ⇒  orb (fv_pt x t1) (fv_pt x t2)
 ]

and fv_pv x v on v ≝
 match v with
 [ pvar y ⇒ veqb x y
 | abstr y t ⇒ if veqb x y then false else fv_pt x t
 ]
 .

lemma env_len: ∀e: Environment. (e = Epsilon → False ) →  S (c_len_e (e_pop e))=(c_len_e e).
#e cases e [ normalize #Abs cut False [ cut (Epsilon=Epsilon) [ //| @Abs] | #Abs
@False_ind] @Abs | #e1 #s #H1 normalize //] qed.

(* Definizione 1: naïve, restituisce il clasico errore: *)
(* NTypeChecker failure: Recursive call (read_back_b b), b is not smaller.

let rec read_back x on x ≝
 match x with
 [ CCrumble b e ⇒ match e with
                  [ Epsilon ⇒ read_back_b b
                  | Cons e1 s ⇒ match s with [ subst x' b1 ⇒ pif_subst (read_back 〈b, e1〉) (psubst x' (read_back_b b1))]
                  ]
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
 | lambda x c ⇒ val_to_term (abstr x (read_back c))
 ]
 .
*)

(* Definizione 2: come da lei consigliato, spezzo la read_back c in read_back b e *)
(* in modo che l'induzione su e mi assicuri la diminuzione della dimensione del termine*)
(* purtroppo però, la chiamata ricorsiva sul byte non mi assicura che la dimensione diminuisca*)
(* suppongo che questo sia dovuto al fatto che un byte può a sua volta contenere un  *)
(* crumble la cui dimensione è arbitraria *)


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

(* Definizione 3: ragionevolmente giusta, ma dà il seguente errore: read_back_b b *)
(* is not smaller. Faccio fatica a capirne il motivo, perché il fatto che la *)
(* lunghezza degli environment dei crumble di livello più esterno diminuisca ad *)
(* ogni chiamata, dovrebbe assicurare la terminazione, ma suppongo anche *)
(* che Matita si aspetti che le chiamate per induzione sulla dimensione di *)
(* un termine abbiano come taglia un intero sempre decrescente, cosa che, con *)
(* la definizione di taglia data da c_len non si verifica. L'errore, dunque, *)
(* dovrebbe somigliare a quello del punto precedente.
*)

(*
let rec read_back (n: nat) : Πc: Crumble. c_len c = n → pifTerm ≝
 match n return λn.Πc: Crumble. c_len c = n → pifTerm with
 [ O ⇒ λc. match c return λc.c_len c = O → pifTerm with
          [ CCrumble b e ⇒ λp.(read_back_b b)]
 | S m ⇒ λc. match c return λc.c_len c = S m → pifTerm with
    [ CCrumble b e ⇒ match e with
        [ Epsilon ⇒  λabs.(read_back_b b)
        | Cons e1 s ⇒ λp.match s with [ subst x' b1 ⇒ pif_subst (read_back m 〈b, e_pop e〉 ?) (psubst x' (read_back_b b1))]
        ]
    ]
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
 | lambda x c ⇒ val_to_term (abstr x (read_back (c_len c) c (refl …)))
 ]
 .

lapply p
normalize cases e normalize [ #H destruct | #e1 #s1 // ]
qed.
*)

(* Definizione 4: provo a definire una funzione size più accurata: la taglia *)
(* di un crumble equivale alla lunghezza ti tutti gli environment in esso *)
(* annidati ney byte al primo membro. In questo modo dovrei riuscire ad evitare l'errore perché *)
(* la suddetta definizione mi garantirebbe la diminuzione della taglia del *)
(* termine ad ogni chiamata ricorsiva. Ma quando vado a fornire la dimostrazione *)
(* mi si solleva un altro problema: come faccio ad esprimere il fatto che e = Cons e1 s ?
*)
(*

let rec read_back (n: nat) : Πc: Crumble. c_size c = n → pifTerm ≝
 match n return λn.Πc: Crumble. c_size c = n → pifTerm with
 [ O ⇒ λc.λabs. ?
 | S m ⇒ λc. match c return λc.c_size c = S m → pifTerm with
    [ CCrumble b e ⇒ match e return λe. c_size (CCrumble b e) = S m → pifTerm with

        [ Epsilon ⇒  λp.(read_back_b (m) b (?))
        | Cons e1 s ⇒ match s return λs. c_size (CCrumble b (Cons e1 s)) = S m → pifTerm with [ subst x' b1 ⇒ λp. pif_subst (read_back ((S m) - (c_size_s [x'← b1])) 〈b, e1〉 ?) (psubst x' (read_back_b (m - c_size 〈b, e1〉) b1 ?))]
        ]
    ]
 ]


and

read_back_b (n: nat): Πb: Byte. c_size_b b = n → pifTerm ≝
 match n return λn.Πb: Byte. c_size_b b = n → pifTerm with
 [ O ⇒ λb. match b return λb. c_size_b b = O → pifTerm with
    [ CValue v ⇒ λp. read_back_v (c_size_v v) v (refl …)
    | AppValue v w ⇒ λabs. ?
    ]
 | S m ⇒ λb. match b return λb. c_size_b b = S m → pifTerm with
    [ CValue v ⇒ λp. read_back_v (c_size_v v) v (refl …)
    | AppValue v w ⇒ λp. appl (read_back_v (c_size_v v) v (refl …)) (read_back_v (c_size_v w) w (refl …))
    ]
 ]

and

read_back_v (n: nat): Πv: Value. c_size_v v = n → pifTerm≝
 match n return λn.Πv: Value. c_size_v v = n → pifTerm with
 [ O ⇒ λv. match v return λv. c_size_v v = O → pifTerm with
     [ var x ⇒ λp.val_to_term (pvar x)
     | lambda x c ⇒ λp.val_to_term (abstr x (read_back (c_size c) c (refl …)))
     ]
 | S m ⇒ λv. match v return λv. c_size_v v = S m → pifTerm with
     [ var x ⇒ λp. val_to_term (pvar x)
     | lambda x c ⇒ λp. val_to_term (abstr x (read_back (c_size c) c (refl …)))
     ]
 ]

 .


(*
[lapply p normalize cases (c_size_b b) [ normalize // | #n cases (c_size_e e1) [
#H // | #p #H cut (S ((S n)+(S p))=S m) [ // | @succ_eq] ] ]  qed.
*)
[ lapply abs cases c #b #e normalize cases (b) [ #v cases (v)[ #x normalize #abs
destruct | #x #d normalize #abs destruct] | #v #w normalize #abs destruct ]
| lapply p normalize //
| normalize in p; destruct normalize cases (c_size_b b1)
 [ normalize // | #q normalize /2/]
|  lapply p normalize #H destruct /2/
| normalize in abs; destruct] qed.
*)

definition ol ≝ λv. fst Value nat (overline v (fresh_var_tv v)).
definition ul ≝ λt. fst Crumble nat (underline_pifTerm t (fresh_var_t t)).

lemma size_lemma:
 (∀t.∀n. c_size (fst  … (underline_pifTerm t n)) ≤ 5 * (t_size t)) ∧
   (∀v.∀n. c_size_v (fst … (overline v n)) ≤ 5 * (v_size v)).

@pifValueTerm_ind
[ #v #H #s normalize lapply (H s) cases (overline v s) #w #n normalize //
| #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s lapply (H1 s) cases (overline v1 s) #vv #n normalize
      #H1' lapply (H2 n) cases (overline v2 n) #ww #m normalize #H2'
      lapply (le_plus … H1' H2') -H1' -H2' #H
      normalize in H1'; <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      cut ((c_size_v vv+c_size_v ww+O)≤(S (S (S (S
       (v_size v1+v_size v2
        +(v_size v1+v_size v2
          +(v_size v1+v_size v2+(v_size v1+v_size v2+(v_size v1+v_size v2+O))))))))))
      [ @le_S @le_S @le_S @le_S //
      | -H #H @le_S_S @H
      ]
    | #u1 #u2 normalize #H1 #H2 #s lapply (H1 s) normalize
      change with (underline_pifTerm (appl u1 u2) s)
       in match (match u2 in pifTerm with [_⇒ ?]);
     cases (underline_pifTerm (appl u1 u2) s)
      * #b #e #n normalize lapply (H2 n) cases (overline v2 n) #vv #mm
      normalize #H2' #H1' <(size_env_push e ?)
      whd in match (c_size_e ?);
      whd in match (c_size_s ?);
      lapply (le_plus … H1' H2') -H1' -H2'
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm 
      cut ((((((t_size u1+t_size u2
        +(t_size u1+t_size u2
          +(t_size u1+t_size u2+(t_size u1+t_size u2+(t_size u1+t_size u2+O)))))))))
   +(v_size v2+(v_size v2+(v_size v2+(v_size v2+(v_size v2+O))))) = (t_size u1+t_size u2+v_size v2
              +(t_size u1+t_size u2+v_size v2
                +(t_size u1+t_size u2+v_size v2
                  +(t_size u1+t_size u2+v_size v2
                    +(t_size u1+t_size u2+v_size v2+O))))))[ //] #HH <HH
       #H @le_S_S @le_S_S @le_S_S @le_S @le_S
       cut (c_size_v vv+(c_size_e e+c_size_b b)=c_size_b b+c_size_e e+(c_size_v vv+O)) [//]
       #HHH >HHH @H
       ]
  | #u1 #u2 normalize #H1 #H2 #s lapply (H2 s)
    change with (underline_pifTerm (appl u1 u2) ?)
      in match ( match u2 in pifTerm with [_⇒ ?]);
    cases (underline_pifTerm (appl u1 u2) s) * #b #e #n normalize
    lapply (H1 n) cases t1
    [ #v1 normalize cases (overline v1 n) #vv #m normalize
      >concat_epsilon_e <(size_env_push e  [νm←b])
      whd in match (c_size_e (Cons e ?));
      whd in match (c_size_s ?);
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
      #H1' #H2'
      @le_S_S @le_S_S @le_S_S @le_S @le_S
      lapply (le_plus …H1' H2') -H1' -H2' #H
      cut (v_size v1+(v_size v1+(v_size v1+(v_size v1+(v_size v1+O))))
    +S
     (S
      (S
       (S
        (S
         (t_size u1+t_size u2
          +(t_size u1+t_size u2
            +(t_size u1+t_size u2+(t_size u1+t_size u2+(t_size u1+t_size u2+O)))))))))=
   (S
    (S
     (S
      (S
       (S (v_size v1+(t_size u1+t_size u2))
        +(v_size v1+(t_size u1+t_size u2)
          +(v_size v1+(t_size u1+t_size u2)
            +(v_size v1+(t_size u1+t_size u2)
              +(v_size v1+(t_size u1+t_size u2)+O))))))))))
   [ <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
     @eq_f @eq_f @eq_f @eq_f @eq_f //
   | #HH <HH >commutative_plus in match (c_size_e e+c_size_b b); @H
   ]
  | #r1 #r2 cases (underline_pifTerm (appl r1 r2) (n)) * #b1 #e1 #n1 normalize
    >(size_env_concat …)
    <(size_env_push e  [νn1←b])
    <(size_env_push e1 [ν(S n1)←b1])
    whd in match (c_size_e (Cons e ?));
    whd in match (c_size_e (Cons e1 ?));
    whd in match (c_size_s ?);
    whd in match (c_size_s ?);
    #H1' #H2'
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    @le_S_S @le_S_S @le_S_S @le_S_S @le_S_S
    lapply (le_plus … H1' H2')
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    cut  (S
   (S
    (S
     (S
      (S
       (S
        (S
         (S
          (S
           (S
            (t_size r1+t_size r2
             +(t_size r1+t_size r2
               +(t_size r1+t_size r2
                 +(t_size r1+t_size r2+(t_size r1+t_size r2+O)))))))))
        +(t_size u1+t_size u2
          +(t_size u1+t_size u2
            +(t_size u1+t_size u2+(t_size u1+t_size u2+(t_size u1+t_size u2+O))))))))))=
  S
    (S
     (S
      (S
       (S
        (S
         (S
          (S
           (S
            (S (t_size r1+t_size r2+(t_size u1+t_size u2))
             +(t_size r1+t_size r2+(t_size u1+t_size u2)
               +(t_size r1+t_size r2+(t_size u1+t_size u2)
                 +(t_size r1+t_size r2+(t_size u1+t_size u2)
                   +(t_size r1+t_size r2+(t_size u1+t_size u2)+O))))))))))))))
   [@eq_f @eq_f @eq_f @eq_f @eq_f normalize //]
   #HH >HH #H
   cut (c_size_e e+c_size_b b+(c_size_e e1+c_size_b b1)=c_size_b b1+c_size_e e1+(c_size_b b+c_size_e e))
   [ // ] #Yee >Yee @H
   ]
 ]
| #x normalize //
| #p #v whd in match (overline ? ?);
  #H cut (t_size p+(t_size p+(t_size p+(t_size p+(t_size p+O))))≤
     (t_size p+S (t_size p+S (t_size p+S (t_size p+S (t_size p+O))))))
  [ <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm <plus_n_Sm
    <plus_n_Sm <plus_n_Sm <plus_n_Sm @le_S @le_S @le_S @le_S  //
  | #H2 #n normalize lapply (H n) cases (underline_pifTerm p n) #c #n normalize -H #H @le_S_S  @(transitive_le … H H2)
] qed.


lemma fv_lemma:
 (∀c.∀x. fvb_t x (read_back c) = true → fvb x c = true) ∧
  (∀b.∀x. fvb_t x (read_back_b b) = true → fvb_b x b = true ) ∧
   (∀e.∀b.∀x. (fvb_t x (read_back_b b)  = true → fvb_b x b = true) → fvb_t x (read_back 〈b, e〉) = true → fvb x 〈b, e〉  = true ) ∧
    (∀v.∀x. fvb_t x (read_back_v v) = true → fvb_v x v = true) ∧
     (∀s.∀b.∀e.∀x. (fvb_t x (read_back 〈b, e〉) = true → fvb x 〈b, e〉 = true ) →  fvb_t x (read_back 〈b, (Cons e s)〉)=true → fvb x 〈b, (Cons e s)〉=true).

@Crumble_mutual_ind
[ #b #e #H1 #H2 #x lapply (H1 x) lapply (H2 b x) #H @H
| #v #H assumption
| #v #w #H1 #H2 #x #H normalize in H;
  change with (appl (read_back_v v) (read_back_v w)) in match (read_back_b ?);
  change with (orb ? ?) in match (if ? then ? else ?) in H;
  whd in match (fvb_t ? ?);
  whd in match (free_occ_t ? ?);
  cut (fvb_t x (read_back_v v)=true ∨ fvb_t x (read_back_v w)=true)
   [ normalize lapply (gtb_O_true … H) #He elim He #j -He
     cases (free_occ_t x (read_back_v v))
     cases (free_occ_t x (read_back_v w))
     [ normalize #abs destruct
     | 2,3,4:  normalize /2/
     ]
   | * #Hrb  change with (fvb_v x v ∨ ?) in match (fvb_b ? ?);
     [ >(H1 x Hrb) //
     | >(H2 x Hrb) /2/
     ]
   ]
| #x #y normalize cases (veqb y x) normalize /2/
| #x #c cases c #b #e normalize #H #y lapply (H y) >(veqb_comm y x) elim (veqb x y) normalize
 [ #Hinutile  // | #Hutile @Hutile]
| #b #x normalize #H #H1 lapply (H H1) #H2 >H2 normalize //
| #e #s cases s #y #b' #H1 #H2 #b #x #H3 lapply (H1 b x) lapply (H2 b e x) #H1' #H2'
  lapply (H2' H3) #H4 lapply(H1' H4) -H1' normalize @sigma_prop_gen #z #_ * #_ #z_prop >z_prop
  <veqb_simm cut (veqb x y=true ∨ veqb x y = false) // * #Htf >Htf normalize
  #Hue #Hyee @(Hue Hyee)
| #y #b #H #b' #e #x
   cases y #ny lapply (H x) #Hx #H1
  whd in match (fvb ? ?); change with (orb ? ?) in match ( if ? then ? else ?);
  change with (aux_read_back ? ?) in match (read_back 〈b',Cons e [νny←b]〉);
  change with (pif_subst (aux_read_back (read_back_b b') e) ?)
    in match (aux_read_back (read_back_b b') (Cons e [νny←b]));
  change with (pi1 … (pif_subst_sig ? ? ? ? ?))
    in match (pif_subst (aux_read_back (read_back_b b') e) (psubst (νny) (read_back_b b)));
  @sigma_prop_gen #z #_ * #_ #z_prop
  change with (gtb ? ?) in match (fvb_t ? ?);
  change with (gtb ? ?) in match (fvb_t x z);
  normalize in match (fvb ? ?);
  >(z_prop x)
   whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
    whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
   change with (read_back 〈b', e〉) in match (aux_read_back (read_back_b b') e);
   change with (gtb (free_occ_t y (read_back_b b)) 0) in match (fvb_t y (read_back_b b)) in Hx;
   change with (gtb (free_occ_t y (read_back 〈b',e〉)) 0) in match (fvb_t y (read_back 〈b',e〉)) in H1;
   whd in match (domb_e ? ?); whd in match (fvb_e ? ?);
   lapply (H x) lapply H1;
   change with (gtb ? ?) in match (fvb_t ? ?);
   change with (gtb ? ?) in match (fvb_t x (read_back_b b));
   cases (free_occ_t x (read_back_b b)) cases (free_occ_t x (read_back 〈b',e〉))
   [ normalize cut ( free_occ_t (νny) (aux_read_back (read_back_b b') e)*O+O=0)
     [ cases  (free_occ_t (νny) (aux_read_back (read_back_b b') e)) //
     | #H0 >H0 >if_monotone whd in match (gtb 0 0); #abs #_ #abs destruct
     ]
   |  #n #Hyess normalize in Hyess; <veqb_simm cut (veqb x (νny)=true ∨ veqb x (νny)=false) // * #Htf
     [ >Htf normalize >if_then_false_else_false >if_then_false_else_false
       normalize >times_O normalize #_ #abs destruct
     | change with (orb ? ?) in match (if veqb x (νny) then true else domb_e x e);
       change with (orb ? ?) in match (if (fvb_e (νny) e∧¬veqb x (νny)) then true else fvb_b x b);
       >Htf change with (domb_e x e) in match (false∨domb_e x e);
       change with true in match (¬false);
       normalize >times_O normalize #_
       change with (notb ?) in match (if domb_e x e then false else true);
       change with (andb ? ?) in match (if fvb_b x b' then (¬domb_e x e) else false);
       >if_then_true_else_false
       change with (orb ? ?) in match (if fvb_e (νny) e then true else fvb_b x b);
       change with (orb ? ?) in match (if ? then ? else ?); #_
       change with (notb ?) in match (if domb_e x e then false else true) in Hyess;
       change with (andb ? ?) in match (if fvb_b x b' then (¬domb_e x e) else false) in Hyess;
       change with (orb ? ?) in match (if ?then ? else ?)in Hyess;
       cut ((fvb_b x b'∧¬domb_e x e∨fvb_e x e)=true)
       [ @Hyess //
       | -Hyess #H4
         cut ((fvb_b x b'∧¬domb_e x e)=true∨fvb_e x e=true)
         [ lapply H4 cases fvb_b cases fvb_e cases domb_e
           normalize /2/
         | * -H4 #H4 >H4 normalize //
         ]
       ]
     ]
   | normalize #H3 #H_ #H5 >H5 // >if_monotone >if_monotone #_ //
   | #n #m normalize #_ #H5 >H5 // >if_monotone >if_monotone #_ //
   ]
] qed.


(*
lemma pif_subst_distro:
 (∀t.∀x, t'. fresh_var_t (pif_subst t (psubst (νx) t')) ≤
  max (fresh_var_t t) (fresh_var_t t')) ∧
 ∀v. (∀x, t'. fresh_var_t (pif_subst (val_to_term v) (psubst (νx) t')) ≤
  max (fresh_var_tv v) (fresh_var_t t')).

@pifValueTerm_ind
[ #v #H cut (∀v. fresh_var_tv v=fresh_var_t (val_to_term v)) //
| #t1 #t2 #H1 #H2 #x #t' >pif_subst_distro
  change with (max (fresh_var_t (pif_subst t1 (psubst (νx) t'))) (fresh_var_t (pif_subst t2 (psubst (νx) t'))))
    in match (fresh_var_t ?);
  cut (max (fresh_var_t (pif_subst t1 (psubst (νx) t')))
           (fresh_var_t (pif_subst t2 (psubst (νx) t')))
       ≤ max (max (fresh_var_t t1) (fresh_var_t t'))
             (max (fresh_var_t t2) (fresh_var_t t')))
  [ @(to_max)
    [ @(le_le_max …) @H1
    | >max_comm @(le_le_max …) @H2
    ]
  |#H change with (max (fresh_var_t t1) (fresh_var_t t2)) in match (fresh_var_t (appl t1 t2));
  <max_fact @H
  ]
| #x #ny #t' cases x #nx cut (veqb (νnx) (νny)=true ∨ veqb (νnx) (νny)=false) // *
  #Htf
  [ lapply (veqb_true_to_eq (νnx) (νny)) * #Heq #_ lapply (Heq Htf) destruct
    -Htf -Heq #Heq destruct >atomic_subst >max_comm
    cut (fresh_var_t t'≤ max ny (fresh_var_t t'))
    [ >max_comm @le_n_max_n
    | #H @(le_le_max …) //
    ]
  | >no_subst //
  ]
| #t #x #H #y #t' lapply (H y t') -H #H
  change with (pi1 … (pif_subst_sig ? ? ? ?)) in match ( pif_subst ? ?);
*)
(*
lemma fresh_var_lemma:
 (∀c. fresh_var_t (read_back c) ≤ fresh_var c) ∧
  (∀b. fresh_var_t (read_back_b b) ≤ fresh_var_b b ) ∧
   (∀e.∀b. (fresh_var_t (read_back_b b) ≤ fresh_var_b b) → fresh_var_t (read_back 〈b, e〉) ≤ fresh_var 〈b, e〉) ∧
    (∀v. fresh_var_t (read_back_v v) ≤ fresh_var_v v) ∧
     (∀s.∀b.∀e. (fresh_var_t (read_back 〈b, e〉) ≤ fresh_var 〈b, e〉) →  fresh_var_t (read_back 〈b, (Cons e s)〉) ≤ fresh_var 〈b, (Cons e s)〉).

@Crumble_mutual_ind
[ #b #e #H #H1 @(H1 b H)
| #v #H whd in match (fresh_var_b (CValue v)); whd in match (read_back_b ?); @H
| #v #w #H1 #H2 whd in match (fresh_var_b (AppValue ? ?));
  change with (max (fresh_var_v ?) (fresh_var_v ?))
   in match (if leb (fresh_var_v v) (fresh_var_v w) then fresh_var_v w else fresh_var_v v);
  whd in match (read_back_b ?);
  change with (max (fresh_var_t (read_back_v v)) (fresh_var_t (read_back_v w))) in match (fresh_var_t ?);
  @(to_max … )
  [ whd in match (max ? ?);
    cut (leb (fresh_var_v v) (fresh_var_v w)=true ∨ leb (fresh_var_v v) (fresh_var_v w)=false) //
    * #Htf >Htf
    [ change with (fresh_var_v w) in match (if true then (fresh_var_v w) else ?);
      lapply (leb_true_to_le … Htf) -Htf #H @(transitive_le … H1 H)
    | change with (fresh_var_v v) in match (if false then ? else (fresh_var_v v));
      @H1
    ]
  | whd in match (max ? ?);
    cut (leb (fresh_var_v v) (fresh_var_v w)=true ∨ leb (fresh_var_v v) (fresh_var_v w)=false) //
    * #Htf >Htf
    [ change with (fresh_var_v w) in match (if true then (fresh_var_v w) else ?);
      @H2
    | change with (fresh_var_v v) in match (if false then ? else (fresh_var_v v));
      lapply (leb_false_to_not_le … Htf) -Htf #H lapply (not_le_to_lt … H) -H #H
      lapply (lt_to_le … H) -H #H @(transitive_le … H2 H)
    ]
  ]
| #x cases x #nx normalize //
| #x cases x #nx #c cases c #b #e normalize
  cases (pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) (aux_read_back (read_back_b b) e)→S x0≤n)
  (fresh_var_t_Sig (aux_read_back (read_back_b b) e)))
  change with (fresh_var 〈b, e〉) in match ((if leb (fresh_var_b b) (fresh_var_e e) 
         then fresh_var_e e 
         else fresh_var_b b));
  [ #H whd in match (match ? in nat with [ _ ⇒ ? ]);
    change with (S nx) in match (if false then O else S nx );
    change with (leb (S nx) ?) in match (match fresh_var 〈b,e〉 in nat return λ_:ℕ.bool with 
        [O⇒false|S (q:ℕ)⇒leb nx q]);
    cut (leb (S nx) (fresh_var 〈b, e〉)=true ∨ leb (S nx) (fresh_var 〈b, e〉)=false) //
    | #k #H change with (leb (S nx) ?) in match (match fresh_var 〈b,e〉 in nat with 
    [O⇒false|S (q:ℕ)⇒leb nx q]);
    change with (leb (S nx) (S k)) in match (match (S k) in nat with 
    [O⇒false|S (q:ℕ)⇒leb nx q]);
    change with (max ? ?) in match (if ? then ? else ?);
    change with (max (S nx) (fresh_var 〈b, e〉)) in match (if (leb (S nx) (fresh_var ?)) then ? else ?);
    @(to_max …)
    change with (if (leb (S nx) (fresh_var 〈b, e〉)) then (fresh_var 〈b, e〉) else (S nx)) in match (max (S nx) ?);
    cut (leb (S nx) (fresh_var 〈b,e〉)=true ∨ leb (S nx) (fresh_var 〈b,e〉)=false) // * #Htf >Htf
    [ lapply (leb_true_to_le … Htf) -Htf #Hle
      change with (fresh_var 〈b,e〉) in match (if true then fresh_var 〈b,e〉 else S nx ); //
    | 3: normalize
    | lapply(leb_false_to_not_le … Htf) -Htf #Hnle
      lapply (not_le_to_lt … Hnle) -Hnle #Hlt
      lapply (lt_to_le … Hlt) -Hlt #Hle
      change with (S nx) in match (if ? then ? else ?);
      @(transitive_le … H Hle)
    ]
  ]
| #b #H whd in match (read_back ?); whd in match (fresh_var ?);
  whd in match (fresh_var_e Epsilon); lapply H cases (fresh_var_b …)
  normalize //
| #e #s #H1 #H2 #b #H @(H2 … (H1 … H))
| * #x #b' #H #b #e #H1 lapply H1
  change with (max ? ?) in match (fresh_var 〈b, e〉);
  change with (max ? ?) in match (fresh_var 〈b, Cons ? ?〉);
  change with (max ? ?) in match (fresh_var_e (Cons e ?));
  change with (max ? ?) in match (fresh_var_s ?);
  whd in match (read_back ?);
  change with (aux_read_back ? ?) in match (read_back ?);
  change with (pif_subst ? ?) in match (aux_read_back ? (Cons ? ?));
  normalize
  @sigma_prop_gen #z #z_def #z_prop
  change with (max ? ?) in match (if ? then ? else ?);
  @sigma_prop_gen #k #k_def #k_prop #Hz
  change with (max ? (max (fresh_var_e e) (max (S x) (fresh_var_b b'))))
    in match (if ? then ? else ?);
  
 
  cut (k ≤ z)
  [ 2:  cut (max (fresh_var_b b) (fresh_var_e e) ≤ 
        max (fresh_var_b b) (max (fresh_var_e e) (max (S x) (fresh_var_b b'))))
    [ //]
    #H1 #H2 @(transitive_le … H2 (transitive_le … Hz H1))
  ]
  lapply ((z_prop k))
   
            #Hf @(transitive_le …
  whd in match (read_back_v ?); lapply H cases c #b #e
  -H #H whd in match (match ? in Crumble with [ _ ⇒ ? ]);
*)


lemma interval_lemma2: ∀e. ∀ (y:Variable).∀ b, n. (interval_dom (Cons e [y←b]) n) → n ≤ match y with [variable ny ⇒ ny].
#e #y #b #n cases y #ny normalize #H @(H ny) lapply (neqb_iff_eq … ny ny) * #_
#Hscontata >Hscontata // qed.

lemma fresh_var_occ:
 (∀t. ∀x. x ≥ (fresh_var_t t) → free_occ_t (νx) t = 0) ∧
  (∀v. ∀x. x ≥(fresh_var_tv v) →  free_occ_v (νx) v = 0).

@pifValueTerm_ind
[ #v #H #x @H
| #t1 #t2 #H1 #H2 #x #H change with (max ? ?) in match (fresh_var_t ?) in H;
  cut (max (pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t1≥1→n>x0) (fresh_var_t_Sig t1))
    (pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t2≥1→n>x0) (fresh_var_t_Sig t2))≤x) //
  -H #H lapply(le_maxl … H) #H11 lapply(le_maxr … H) #H22 -H
  cut (x ≥pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t1≥1→n>x0) (fresh_var_t_Sig t1)) // -H11 #H11
  cut (x ≥pi1 ℕ (λn:ℕ.∀x0:ℕ.free_occ_t (νx0) t2≥1→n>x0) (fresh_var_t_Sig t2)) // -H22 #H22
  lapply (H1 … H11) lapply (H2 x H22) -H1 -H11 -H2 -H22 #H2 #H1
  change with (plus ? ?) in match (free_occ_t ? ?); //
| #x cases x #nx normalize #y #H cut (neqb y nx = true ∨ neqb y nx = false) // *
  #Htf [2: >Htf // | @False_ind lapply (neqb_iff_eq y nx) * #Heq #_ lapply (Heq Htf)
  -Htf -Heq #Heq destruct @(leq_Sx_x_false nx H)]
| #t #x #HI #y whd in match (fresh_var_tv ?); whd in match (fresh_var_tv_Sig ?);
  cases x #nx normalize
  change with (leb (S nx) ?) in match (match pi1 ℕ (λn:ℕ.∀x00:ℕ.1≤free_occ_t (νx00) t→S x00≤n) (fresh_var_t_Sig t)
        in nat
        return λ_:ℕ.bool
        with 
       [O⇒false|S (q:ℕ)⇒leb nx q]);
  change with (max ? ?) in match (if ? then ? else ?);
  #H lapply(le_maxl … H) #H1 lapply(le_maxr … H) #H2 -H
  cut (y≥(pi1 ℕ (λn:ℕ.∀x00:ℕ.1≤free_occ_t (νx00) t→S x00≤n) (fresh_var_t_Sig t))) //
  -H2 #H2 >(HI y H2) cases (neqb y nx) //
] qed.
(*
lemma pif_subst_lemma: ∀t, t', ny. fresh_var_t t ≤ ny → pif_subst t (psubst (νny) t')=t.
#t #t' #ny #H
change with (pi1 … (pif_subst_sig (t_size t) ? t ?)) in match (pif_subst ??);
@(nat_ind … (t_size t));
normalize () t @sigma_prop_gen cases (t_size t) #z #z_def * #_ #z_prop
*)

lemma fresh_var_abstr: ∀x,t,ny. fresh_var_t (val_to_term (abstr x t)) ≤ ny → veqb x (νny) =false.
#x #t #ny cut (veqb x (νny)=true ∨ veqb x (νny)=false) // * #Hveqb [2: //]
lapply (veqb_true_to_eq x (νny)) * #Heq #_ lapply (Heq Hveqb) -Hveqb -Heq #Heq
destruct >veqb_true normalize  change with (leb (S ny) ?) in match (match pi1 ℕ (λn:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t→S x0≤n) (fresh_var_t_Sig t)
         in nat
         return λ_:ℕ.bool
         with 
        [O⇒false|S (q:ℕ)⇒leb ny q])  ;
        change with (max ? ?) in match (if ? then ? else ?);
#H lapply(le_maxl … H) #abs -H @False_ind /2/ qed.

lemma aux_read_back1: ∀t1, t2, e. aux_read_back (appl t1 t2) e = appl (aux_read_back t1 e) (aux_read_back t2 e).
#t1 #t2 #e @(Environment_simple_ind2 … e)
[ normalize //
| #e' #s cases s #x #b
  change with (pif_subst (aux_read_back (appl t1 t2) e') (psubst x (read_back_b b)))
  in match (aux_read_back (appl t1 t2) (Cons e' [x←b]));
  change with (pif_subst (aux_read_back t1 e') (psubst x (read_back_b b)))
  in match (aux_read_back t1 (Cons e' [x←b]));
  change with (pif_subst (aux_read_back t2 e') (psubst x (read_back_b b)))
  in match (aux_read_back t2 (Cons e' [x←b]));
  #HI >HI @pif_subst_distro
] qed.

lemma push_lemma_aux: ∀t, e, s. aux_read_back t (Cons e s) = aux_read_back (aux_read_back t e) (Cons Epsilon s).
#t #e @(Environment_simple_ind2 … e)
[ #s normalize in match ((aux_read_back t Epsilon)); //
| #e' #s' #H #s lapply (H s')
 cases s' #y #b #H' >H' /2/
]. qed.


lemma push_lemma:
 ∀t, e, s. aux_read_back t (push e s) = aux_read_back (pif_subst t match s with [subst x b ⇒ psubst x (read_back_b b) ]) e.
 #t #e @(Environment_simple_ind2 … e)

[ normalize #s cases s #x #b normalize //
| #e' #s' #H #s lapply (H s)
  normalize in match (push ? ?) in ⊢ (? → %);
  cases s #y #t
  normalize in match (match [y←t]  with 
    [subst (x:Variable)   (b:Byte)⇒psubst x (read_back_b b)]);
  #H' >(push_lemma_aux …) /2/
] qed.

lemma fresh_dom_e: ∀x, e. domb_e (νx) e =true → x ≤ fresh_var_e e.
#x #e @(Environment_simple_ind2 … e)
[ normalize #abs destruct
| #e' * * #ny #b normalize change with (leb (S ny) ?) in match (match fresh_var_b b in nat with 
                [O⇒false|S (q:ℕ)⇒leb ny q]);
  change with (max ? ?) in match (if leb ? ? then ? else ? );
  change with (max ? ?) in match (if leb (S ny) ? then ? else ? );
  cut (neqb x ny=true ∨ neqb x ny=false) // * #Htf >Htf
  [ >if_t lapply (neqb_iff_eq … x ny) * #Heq #_ lapply (Heq Htf) -Heq
    #Heq destruct #_ #_ >max_comm cut (ny ≤S ny) // #Hw
    cut (S ny≤max (max (S ny) (fresh_var_b b)) (fresh_var_e e'))
    [ /2/
    | #H @le_le_max cut (S ny ≤max (S ny) (fresh_var_b b))[ @le_n_max_n | #HH @le_le_max assumption]
    ]
  | >if_f #H #HH lapply (H HH) -H -HH #H @le_le_max assumption
  ]
qed.
axiom pif_subst_lemma: ∀ny.
 (∀t. fresh_var_t t ≤ ny → ∀t'. pif_subst t (psubst (νny) t')=t).

(*
il lemma seguente non è dimostrabile in questa formulazione perché la pif_subst
effettua α-conversioni anche senza che avvenga la sostituzione,
l'uguaglianza fra un termine ed il suo sostituito è dunque vera se intesa come
equivalenza a meno di α-conversioni
*)

(*
lemma pif_subst_lemma: ∀ny.
 (∀t. fresh_var_t t ≤ ny → ∀t'. pif_subst t (psubst (νny) t')=t) ∧
  ∀v. fresh_var_tv v ≤ ny →∀t'. pif_subst (val_to_term v) (psubst (νny) t')=(val_to_term v).

#ny @pifValueTerm_ind
[ 3: #x #H #t' whd in match (pif_subst_sig  ? ? ? ? );
  cut (∀gg.∀ tt. (pi1 pifTerm
  (λu:pifTerm
   .t_size u
    =(t_size (val_to_term (pvar x)))
     +((free_occ_t (νny) (val_to_term (pvar x)))*(t_size t'-1))
    ∧(∀z:Variable
      .free_occ_t z u
       =if match z in Variable return λ_:Variable.bool with 
             [variable (m1:ℕ)⇒neqb ny m1] 
        then (free_occ_t z (val_to_term (pvar x)))*(free_occ_t z t') 
        else (free_occ_t (νny) (val_to_term (pvar x)))*(free_occ_t z t')
                 +free_occ_t z (val_to_term (pvar x)) ))
 (match veqb (νny) x
 return λb. veqb (νny) x = b → 1 ≤ 1 →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb (νny) x = true.
        λp: 1 ≤ 1.
         «t', gg H p»
     | false ⇒ λH: veqb (νny) x = false.
        λp: 1 ≤ 1.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb (νny) x )) (le_n 1))) = val_to_term (pvar x))
     [2: #UU @UU]  #gg #tt
     lapply (fresh_var_occ) * #fv_occ #_
     cut (free_occ_t (νny) (val_to_term (pvar x))=0)
     [ @fv_occ //
     | cut (veqb (νny) x=true ∨ veqb (νny) x=false ) // *
     #Hveqb
     [ lapply (veqb_true_to_eq (νny) x) * #Heq #_
       lapply (Heq Hveqb) -Heq #Heq destruct #abs
       normalize in abs; normalize in Hveqb;>Hveqb in abs;
       #abs normalize in abs; destruct
     | >Hveqb in gg tt ⊢ %; normalize #_ #_ #_ //
     ]
   ]
| 4: #r #x #HI #H #t' whd in match (pif_subst_sig  ? ? ? ? );
  whd in match (match ? in pifSubst with [_ ⇒ ?]);
  whd in match (match ? in pifSubst with [_ ⇒ ?]);
  cut (∀K.∀K1.∀K2. (pi1 pifTerm   (λu:pifTerm
   .t_size u
    =(t_size (val_to_term (abstr x r)))
     +(free_occ_t (νny) (val_to_term (abstr x r)))*(t_size t'-1)
    ∧(∀z:Variable
      .free_occ_t z u
       =if match z in Variable return λ_:Variable.bool with 
             [variable (m1:ℕ)⇒neqb ny m1] 
        then (free_occ_t z (val_to_term (abstr x r)))*(free_occ_t z t' )
        else (free_occ_t (νny) (val_to_term (abstr x r)))*(free_occ_t z t')
                 +(free_occ_t z (val_to_term (abstr x r))) ))
  (match veqb (νny) x return λb. veqb (νny) x = b → t_size (val_to_term (abstr x r)) ≤ S (t_size r) → Σu: pifTerm. ?
      with
       [ true ⇒ λH:veqb (νny) x = true.λp:t_size (val_to_term (abstr x r)) ≤ S (t_size r). «(val_to_term (abstr x r)), K H p »
       | false ⇒ λH:veqb (νny) x = false. match fvb_t x t'return λb. fvb_t x  t' = b → t_size (val_to_term (abstr x r)) ≤ S (t_size r) → Σu: pifTerm. ?
        with
         [ true ⇒ λHH:fvb_t x  t' = true. λp:t_size (val_to_term (abstr x r)) ≤ S (t_size r). let z ≝ (max (S ny) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t r) (fresh_var_t t'))))
                  in match (pif_subst_sig (t_size r) (psubst x (val_to_term (pvar ν(z)))) r (le_n ?)) with
           [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size r) (psubst (νny) t') a (subst_aux_5 r x z a (t_size r) h p))))), K1 H HH p a h »]
         | false ⇒ λHH:fvb_t x  t' = false. λp. «(val_to_term (abstr x (pi1 … (pif_subst_sig (t_size r) (psubst (νny) t') r (le_n ?))))), K2 H HH p»
         ] (refl …)
       ] (refl bool (veqb (νny) x)) (le_n (t_size (val_to_term (abstr x r)))))=val_to_term (abstr x r)))
       [2: #UU @UU] #K #K1 #K2
       lapply (fresh_var_occ) * #fv_occ #_
     cut (free_occ_t (νny) (val_to_term (abstr x r))=0)
     [@fv_occ //
     | lapply(fresh_var_abstr …H) #Hveqb  check veqb_comm lapply (veqb_comm x (νny)) #Hcomm <Hcomm in K K1 K2 ⊢ %;
        #K #K1 #K2 >Hveqb in K K1 K2 ⊢ %; lapply (fresh_var_abstr_decr x r) #Hm
        lapply (HI (transitive_le … Hm H)) -HI #HI  #K #K1 #K2
        cut (fvb_t x t'=true ∨ fvb_t x t'=false) // * #Hfvb_t >Hfvb_t in K K1 K2 ⊢ %;
        [ 2:  #K #K1 #K2 #FreeOcc normalize in HI; normalize @eq_f @eq_f @HI
        | #K #K1 #K2 #Hfo whd in match (pi1 …); normalize >HI
        change with (pif_subst r (psubst (νny) t')) in match (pif_subst_sig (t_size r) (psubst (νny) t') r
                                 (le_n (t_size r))); normalize in HI;
        cut (∀K. (pi1 pifTerm
   (λu:pifTerm
    .t_size u=t_size r+(free_occ_t (νny) r)*(t_size t'-1)
     ∧(∀z:Variable
       .free_occ_t z u
        =if match z in Variable return λ_:Variable.bool with 
              [variable (m1:ℕ)⇒neqb ny m1] 
         then (free_occ_t z r)*(free_occ_t z t') 
         else (free_occ_t (νny) r)*((free_occ_t z t')+(free_occ_t z r)) ))
   (pif_subst_sig (t_size r) (psubst (νny) t') r (K (t_size r)))
   =r));


         >HI in K K1 K2 ⊢ %; normalize // check veqb_comm normalize #_ #_ #_ //
     ]




      >Hfv_occ in K K1 K2 ⊢ %;
*)

lemma aux_read_back3: ∀t, e, b.
  (fresh_var_t t ≤ b) →
   (interval_dom e b) → (*interval_dom ≝  λe, b. ∀x. domb_e (νx) e =true → b ≤ x.*)
     aux_read_back t e = t.

#t #e #b #H1
@(Environment_simple_ind2 … e)
[ normalize //
| #e' #s' #HI #H1 lapply (HI (interval_lemma … H1)) #H2
  lapply H1 cases s' #y #b' -H1 #H1
  change with (pif_subst (aux_read_back t e') (psubst y (read_back_b b')))
  in match (aux_read_back t (Cons e' [y←b'])) ; >H2
  lapply (interval_lemma2 … e' y b' b H1) cases y #ny #Hforte
  normalize in Hforte; @pif_subst_lemma /2/
] qed.

lemma aux_read_back4: ∀m,e.
 fresh_var_e e ≤ m → 
  (aux_read_back (val_to_term (pvar νm)) e=val_to_term (pvar νm)).

#m #e @(Environment_simple_ind2 … e)
[ normalize //
| #e' * * #y #b #HI
  change with (max ? ?) in match (fresh_var_e ?); #Hm
  lapply (HI (le_maxl … Hm)) -HI #HI
  change with (pif_subst ? ?)
    in match (aux_read_back ? ?);
  >HI @no_subst
  lapply (le_maxr … Hm)
  change with (max ? ?) in match (fresh_var_s ?);
  #Hm1 normalize
  cut (neqb y m=true ∨ neqb y m=false) // * // #Htf
  lapply (neqb_iff_eq y m) * #Heq #_
  lapply (Heq Htf) -Heq #Heq destruct
  lapply (le_maxl … Hm1) /2/
] qed. 
  

(*
lemma basic_subst: ∀x, t. (pif_subst (val_to_term (pvar x)) (psubst x t)) = t.
#x #t change with (pi1 … (pif_subst_sig (t_size ?) ? ? ?)) in match (pif_subst ??);
change with (1) in match (t_size (val_to_term (pvar x)));
whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
whd in match (pif_subst_sig 1 (psubst x t) (val_to_term (pvar x)) (le_n 1));
lapply(veqb_true x) #Ht cases (veqb x x)


lemma definetly_simple_concat_lemma:
 ∀e, s. (concat e (Cons Epsilon s) = Cons e s).

@Environment_simple_ind2
[ #s normalize //
| #e' #s' #H #s normalize >H //
] qed. 

lemma abba_difficult_concat_lemma:
 ∀f, e, x, s. match s with [subst y b ⇒ match y with [variable nx ⇒ nx] ] ≥ S x → interval_dom e (S x) → 
  aux_read_back (val_to_term (pvar νx)) (concat e (push f s)) =
   aux_read_back (val_to_term (pvar νx)) (concat e f).
   
#f

@(Environment_simple_ind2 … f)
[ #e #x * * #y #b #H #H1
  whd in match (concat ? ?);
  >banal_concat_lemma
  change with (pif_subst ? ? )
    in match (aux_read_back ? (Cons ? ?));
  >(aux_read_back3 … (S x))
  [ >(no_subst …  (νx) (νy) (read_back_b b)) //
    normalize cut (neqb y x = true ∨ neqb y x = false) // * #Htf
    [ lapply (neqb_iff_eq y x) * #Heq #_ lapply (Heq Htf) -Heq #Heq
      destruct @False_ind /2/
    | @Htf
    ] 
  | @H1 
  | //
  ]
| #e #s #H #f' #x * * #y #b
  whd in match (match ? in Substitution with [_ ⇒ ?]); 
  whd in match (push ? ?);
  @(Environment_simple_ind2 … e)
  [ normalize #H1 #H2
    whd in match ((concat f' (Cons (Cons Epsilon [νy←b]) s)));
 
whd in match (concat e (Cons Epsilon ?));
*)
lemma ultimate_concat_lemma:
  (∀x, f, e. interval_dom e (S x) →  (aux_read_back (val_to_term (pvar (νx)))
  (concat e f)
  =aux_read_back (val_to_term (pvar νx)) f)).
  
#x #f @(Environment_simple_ind2 … f)
[ #f #H whd in match (concat ? ?); >(aux_read_back3 … (S x)) //
| #e' * * #y #b #HI #e
  whd in match (concat e (Cons e' ?));
  #Hdom (*fattibile*)
  change with (pif_subst  ? ?) in match (aux_read_back (val_to_term (pvar (νx))) (Cons (concat e e') ?));
  >HI //
] qed.

lemma ultra_concat_lemma:
  (∀x, f, e. x ≥ fresh_var_e e →  (aux_read_back (val_to_term (pvar (νx)))
  (concat e f)
  =aux_read_back (val_to_term (pvar νx)) f)).

#x #f
@(Environment_simple_ind2 … f)
[ #e #H >concat_e_epsilon
  whd in match (aux_read_back (val_to_term (pvar νx)) Epsilon);
  lapply H
  @(Environment_simple_ind2 … e)
  [ //
  | #e' *
   * #y #b #HI #H'
    normalize in H'; 
    change with (max (fresh_var_e e') (max (S y) ?)≤ x) in H';
    change with (pif_subst ? ?) in match (aux_read_back ? ?);
    >(HI … (le_maxl … H'))
    >(no_subst (νx) (νy) (read_back_b b)) //
    lapply (le_maxl … (le_maxr … H'))
    #Hle normalize
    cut (neqb y x=true ∨ neqb y x=false) // * #Htf //
    lapply (neqb_iff_eq y x) * #Heq #_ lapply (Heq Htf)
    -Heq #Heq destruct @False_ind /2/
  ]
| #f' * * #y #b  #HIe #e'
  whd in match (concat ? ?); #H
  change with (pif_subst ? ?)
    in match (aux_read_back ? ?);
  change with (pif_subst ? ?)
    in match (aux_read_back ? (Cons ? ?));
  >HIe //
] qed.

lemma iper_concat_lemma:
 ∀m, n, e, f, b, b1.
  fresh_var_e e ≤ m → fresh_var_b b ≤ m → 
   fresh_var_e f ≤ n → fresh_var_b b1 ≤ n →
    interval_dom e n →  n≤m → 
   ((aux_read_back (val_to_term (pvar νm))
    (concat (push f [(νm)←b1]) (push e [ν(S m)←b]))
    =aux_read_back (val_to_term (pvar νm)) (push f [(νm)←b1]))).

#m #n #e @(Environment_simple_ind2 … e)

[ #f #b #b1
  whd in match (push ? ?);
  change with (Cons ? ?) in match (concat (push f [νm←b1]) (Cons Epsilon [ν(S m)←b]));
  >concat_e_epsilon
  #_ #Hfvb #Hfvf #Hfvb1 #_ #Hnm
  change with (pif_subst ? ?) in match (aux_read_back ? (Cons (push f ?) ?)); 
  change with (read_back 〈 CValue (var ?), push f ?〉)
    in match ((aux_read_back (val_to_term (pvar νm)) (push f ?)));
  lapply fv_lemma * * * * #Hc #Hb #He #Hv #_ 
  lapply (Hc 〈CValue (var νm),(push f [νm←b1])〉 ν(S m)) #Hfv
  whd in match (read_back ?) in Hfv ⊢ %;
  whd in match (read_back_b ?);
  cut (fvb (ν(S m)) 〈CValue (var (νm)),(push f [νm←b1])〉=false → fvb_t (ν(S m)) (aux_read_back (read_back_b (CValue (var νm))) (push f [νm←b1]))=false)
  [ lapply Hfv cases fvb_t cases fvb // #Ht #_ >Ht //
  | -Hfv #Hfv
    cut (fvb (ν(S m)) 〈CValue (var νm),(push f [νm←b1])〉=false)
    [ change with (((fvb_b ? ?) ∧ ¬(domb_e ? ?)) ∨ fvb_e ? ?)
       in match (fvb ? ?);
      change with (neqb ? ?) in match (fvb_b (ν (S m)) (CValue (var (νm))));
      cut (neqb (S m) m =false) [//] #Hf >Hf
      change with (fvb_e (ν(S m)) (push f [νm←b1])=false) -Hf
      cut (inb_e (ν (S m)) (push f [νm←b1]) = false)
      [ lapply (fresh_var_to_in_crumble) * * * * #_ #_ #Hfvtoin #_ #_
      | #Hin lapply fv_to_in_crumble * * * * #_ #_ #Hine #_ #_
        lapply (Hine (push f [νm←b1]) ν(S m)) -Hine #Hinf
        cut (inb_e (ν(S m)) (push f [νm←b1])=false → fvb_e (ν(S m)) (push f [νm←b1])=false)
        [ lapply Hinf cases fvb_e cases inb_e // #Ht >Ht //
        | -Hinf #Hinf >Hinf //
        ]
      ] @Hfvtoin <fresh_var_push
      change with (max ? (max ? ?)) in match (fresh_var_e ?);
      @to_max
      [ @(le_S … (transitive_le … Hfvf Hnm))
      | @to_max // @(le_S … (transitive_le … Hfvb1 Hnm))
      ]
    | #HH whd in match (read_back_b ?) in Hfv; lapply Hfv
      letin t ≝ ((val_to_term (pvar νm)))
      letin z ≝ (aux_read_back t (push f [νm←b1])) -Hfv #Hfv
      lapply (Hfv HH) -Hfv #Hfv
      lapply no_subst4 * #Hnos1 #_ @Hnos1 @Hfv
    ]
  ]
| #e' * * #y #b' #HI #f #b #b1
  change with (max ? (max ? ?)) in match (fresh_var_e (Cons ? ?));
  #H1 #H2 #H3 #H4 #H5 #H6
  whd in match (push (Cons ? ?) ?);
  whd in match (concat ? ?);
  change with (pif_subst ? ?) in match (aux_read_back ? (Cons (concat ? ?) ?));
  >(HI … (le_maxl … H1) H2 H3 H4 (interval_lemma … H5) H6)
  lapply no_subst4 * #Hns1 #_ @Hns1
  cut  (fvb_t (νy) (aux_read_back (val_to_term (pvar νm)) (push f [νm←b1]))
        =true ∨
        fvb_t (νy) (aux_read_back (val_to_term (pvar νm)) (push f [νm←b1]))
        =false) // * #Htf //
  @False_ind lapply fv_lemma * * * * #Hc #Hb #He #Hv #Hs
  lapply Htf
  change with (read_back 〈CValue (var νm), (push f [νm←b1])〉) 
  in match (aux_read_back ? ?);
  #Htf' lapply (Hc … Htf') normalize
  cut ((neqb y m=false) ∧ (fvb_b (νy) b1=false) ∧ (inb_e (νy) f=false))
  [ %
    [ %
      [ lapply (le_maxl … (le_maxr … H1))
        cut (neqb y m = true ∨ neqb y m = false) // * #Htf //
        lapply (neqb_iff_eq y m) * #Heq #_ lapply (Heq Htf) -Heq #Heq
        >Heq /2/
      | lapply (H5 y) normalize >neqb_refl >if_t lapply H4
        lapply fresh_var_to_in_crumble * * * * #_ #Hfvb #_ #_ #_
        #Ht1 #Ht2 
        lapply fv_to_in_crumble * * * * #_ #Hb' #_ #_ #_
        lapply (Hb' b1 (νy)) -Hb' #Hb'
        cut (inb_b (νy) b1=false → fvb_b (νy) b1=false)
        [ lapply Hb' cases fvb_b cases inb_b // #H #_ >H //
        | -Hb' #Hb' >Hb' // @Hfvb cut (n≤y) [@Ht2 //] -Ht2 #Ht2
          @(transitive_le … Ht1 Ht2)
        ]
      ]
    | lapply (H5 y) normalize >neqb_refl >if_t
      #Hny cut (n≤y) [ @Hny //] -Hny #Hny
      cut (fresh_var_e f≤ y)
      [ @(transitive_le … H3 Hny)
      | lapply fv_to_in_crumble * * * * #_ #_ #He' #_ #_
        lapply (He' f (νy)) -He' #He'
        lapply fresh_var_to_in_crumble * * * * #_ #_ #He'' #_ #_
        @He'' @Hfve
      ]
    ]
  ] * * #Hneqb >Hneqb >if_f #Hfvb1
    @(Environment_simple_ind2 … f)
    [ normalize >Hfvb1 #_ #abs destruct
    | #f' * #g #t #HI' whd in match (push ? ?);
      change with (((fvb_e (νy) ?) ∧ (¬ veqb (νy) g)) ∨ fvb_b (νy) t)
        in match (fvb_e (νy) (Cons (push ? [νm ← b1]) [g←t]));
      change with (((fvb_e (νy) f') ∧ (¬ veqb (νy) g)) ∨ fvb_b (νy) t)
        in match (fvb_e (νy) (Cons f' [g←t]));
      #Hnonso
      cut (inb_b (νy) t =false)
      [ cut (inb_b (νy) t =true ∨ inb_b (νy) t =false) // * #Ht //
        @False_ind lapply Hnonso normalize >Ht 
        lapply fv_to_in_crumble * * * * #_ #Hbb #_ #_ #_
        normalize >if_monotone >if_monotone #abs destruct
      ]
      #Hinyt
      cut (fvb_b (νy) t =false)
      [ lapply fv_to_in_crumble * * * * #_ #Hb' #_ #_ #_
        lapply (Hb' t (νy)) -Hb' #Hb'
        cut (inb_b (νy) t=false → fvb_b (νy) t=false)
        [ lapply Hb' cases inb_b cases fvb_b // #H >H // ]
        -Hb'#Hb' @Hb' assumption
      ]
      #Hfvt lapply Hnonso -Hnonso >Hfvt
      #Hdino #Hsauri @HI'
      [ lapply Hdino normalize cases inb_b
        [ >if_monotone >if_monotone #abs destruct
        | cases inb_e normalize //
        ]
      | cut (veqb (νy) g=false)
        [ lapply Hdino cases g normalize #ng cases neqb // >if_monotone //]
        #Hyg lapply Hsauri >Hyg normalize
        >if_then_true_else_false >if_then_true_else_false //
        ]
      ]
    ] qed.  
  
lemma four_dot_two:
    (∀t.∀s. (s ≥ fresh_var_t t) → read_back (fst ?? (underline_pifTerm t s)) = t ) ∧
    (∀v.∀s. (s ≥ fresh_var_tv v) →read_back_v (fst ?? (overline v s)) = val_to_term v).

@(pifValueTerm_ind (λt.∀s. (s ≥ fresh_var_t t) → read_back (fst ?? (underline_pifTerm t s)) = t)
      (λv.∀ s. (s ≥ fresh_var_tv v) →read_back_v (fst ?? (overline v s)) = val_to_term v ))
[ #v normalize in match (fresh_var_tv ?); #HI #s #Hsz lapply (HI s Hsz)
 -HI -Hsz normalize cases (overline v s) #vv #nn normalize //
| lapply line_monotone_names * #Hmono1 #Hmono2 #t1 #t2 cases t2
  lapply (line_names) * #Hline1 #Hline2
  [ #v2
    cases t1
    [ #v1 normalize #H1 #H2
      #s lapply (H1 s) lapply (Hmono2 v1 s) cases (overline v1 s) #vv #n normalize
      #Hsn -H1 #H1 lapply (H2 n) lapply (Hmono2 v1 n) cases (overline v2 (n))
      #ww #m normalize #Hnm -H2 #H2 change with (max ? ?) in match (if ? then ? else ?);
      #Hmax lapply (le_maxl … Hmax) lapply (le_maxr … Hmax) -Hmax #H2' #H1'
      lapply (H1 H1') lapply (H2 (transitive_le … H2' Hsn )) -H2 -H2' -H1 -H1'
      #H1 #H2 >H1 >H2 //
    | #u1 #u2 normalize #Hu1u2 #Hv2 #s lapply (Hu1u2 s)    
      change with (underline_pifTerm (appl u1 u2) s) in match
      (match u2 in pifTerm with [_ ⇒ ?]);
      lapply (Hmono1 (appl u1 u2) s)
      lapply (line_dom (appl u1 u2) s)
      cases (underline_pifTerm (appl u1 u2) s) * #b #e #n normalize #Hdome #Hsn
      lapply (Hv2 n) lapply (Hmono2 v2 n)
      cases (overline v2 n) #vv #m normalize #Hnm
      change with (max ? ?) in match (if leb ? ? then ?  else ?);
      change with (fresh_var_tv ?) in match (pi1 nat ? ?); 
      change with (fresh_var_t ?) in match (pi1 nat ? (fresh_var_t_Sig u1));
      change with (fresh_var_t ?) in match (pi1 nat ? (fresh_var_t_Sig u2)); 
      change with (max ? ?) in match (if leb (max ? ?) ? then ? else ?);
      #H2 #H1 #H lapply (H1 (le_maxl … H)) -H1 #H1
      lapply (H2 (transitive_le … (le_maxr … H) Hsn)) -H2 #H2 >H2
      >(aux_read_back1 (val_to_term (pvar ν(m))) (val_to_term v2) (push e [ν(m)←b]))
      >(push_lemma …)
      change with (psubst ? (read_back_b ?)) in match (match [ν(m)←b] return λ_:Substitution.pifSubst with 
        [subst (x:Variable)   (b0:Byte)⇒psubst x (read_back_b b0)]);
      >(atomic_subst …)  >H1 @eq_f >(aux_read_back3 … (s))
      [ //
      | normalize #x lapply (Hdome x) -Hdome #Hdome >dom_push normalize
        cut (neqb x (m)=true ∨ neqb x (m)=false) // * #Htf
        [ lapply (neqb_iff_eq x (m)) * #Heq #_ lapply (Heq Htf)
          -Heq #Heq destruct >neqb_refl >if_t #_ @(transitive_le … Hsn Hnm)
        | >Htf >if_f #H @(Hdome H)
        ]
      | normalize @(le_maxr … H)
      ]
    ]
  | #u1 #u2 #H1 #H2 #s lapply (H2 s)
    lapply (Hline1 (appl u1 u2) s)
    lapply (line_dom (appl u1 u2) s)
    lapply (Hmono1 (appl u1 u2) s) normalize
    change with (underline_pifTerm (appl u1 u2) s)
      in match (match u2 in pifTerm with [_ ⇒ ?]);
    cases ((underline_pifTerm (appl u1 u2) s)) * #b1 #e1 #n normalize
    #Hsn #Hdome1
    lapply (H1 (n)) cases t1
    [ #v1 normalize
      lapply (Hline2 v1 n)
      lapply (Hmono2 v1 n)
      cases (overline v1 n) #vv #m normalize #Hnm
      change with (fresh_var_tv ?) 
        in match (pi1 … (fresh_var_tv_Sig v1));
      change with (fresh_var_t ?)
        in match (pi1 … (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 … (fresh_var_t_Sig u2));
      #Hline2
      change with (max ? ?) in match (if leb ? ? then ? else ?); #H1'
      change with (max (fresh_var_b b1) ?)
        in match (if leb (fresh_var_b b1) ? then ? else ?); #Hline1 #H2'
      change with (max ? ?) in match (if leb (fresh_var_tv v1) (max (fresh_var_t u1) (fresh_var_t u2)) 
                                      then max (fresh_var_t u1) (fresh_var_t u2) 
                                      else fresh_var_tv v1); #H
      lapply (H1' (transitive_le … (le_maxl … H) Hsn)) -H1' #H1'
      lapply (H2' (le_maxr … H)) -H2' #H2'
      >aux_read_back1 >concat_epsilon_e >push_lemma >push_lemma
      change with (psubst ? (read_back_b ?)) in match (match [ν(m)←b1] return λ_:Substitution.pifSubst with 
        [subst (x:Variable)   (b0:Byte)⇒psubst x (read_back_b b0)]);
      >atomic_subst >H2' @eq_f2 // >H1'
      >(aux_read_back3 … (s))
      [ cut (inb_t (νm) (val_to_term v1) = false)
        [ lapply (transitive_le … (transitive_le … (le_maxl … H) Hsn) Hnm)
          normalize lapply fresh_var_to_in * #_ #Hin #Htmp
          @(Hin … Htmp)
        | lapply no_subst3 * #Hnsbst #_ #Hy > (Hnsbst … Hy ) //
        ]
      | @Hdome1
      | cut (inb_t (νm) (val_to_term v1) = false)
        [ lapply (transitive_le … (transitive_le … (le_maxl … H) Hsn) Hnm)
          normalize lapply fresh_var_to_in * #_ #Hin #Htmp
          @(Hin … Htmp)
        | lapply no_subst3 * #Hnsbst #_ #Hy > (Hnsbst … Hy) @(le_maxl …H)
        ]
      ]
    | #r1 #r2
      lapply (Hline1 … (appl r1 r2) n)
      lapply (line_dom (appl r1 r2) n)
      lapply (Hmono1 … (appl r1 r2) n)
      cases (underline_pifTerm (appl r1 r2) n)
      * #b #e #m normalize #Hnm #Hdome
      change with (fresh_var_t ?)
        in match (pi1 … (fresh_var_t_Sig r1));
      change with (fresh_var_t ?)
        in match (pi1 … (fresh_var_t_Sig r2));
      change with (fresh_var_t ?)
        in match (pi1 … (fresh_var_t_Sig u1));
      change with (fresh_var_t ?)
        in match (pi1 … (fresh_var_t_Sig u2));
      change with (max ? ?) in match ((if leb (fresh_var_t r1) (fresh_var_t r2) 
          then fresh_var_t r2 
          else fresh_var_t r1 ));
      change with (max ? ?) in match ((if leb (fresh_var_t u1) (fresh_var_t u2) 
          then fresh_var_t u2 
          else fresh_var_t u1 ));
      change with (max ? ?) in match (if leb (fresh_var_b b) (fresh_var_e e) 
          then fresh_var_e e 
          else fresh_var_b b);
      change with (max ? ?) in match (if leb (fresh_var_b b1) (fresh_var_e e1) 
          then fresh_var_e e1 
          else fresh_var_b b1);
      change with (max ? ?) in match (if leb (max (fresh_var_t r1) (fresh_var_t r2))
         (max (fresh_var_t u1) (fresh_var_t u2)) 
         then max (fresh_var_t u1) (fresh_var_t u2) 
         else max (fresh_var_t r1) (fresh_var_t r2)
         );
      #Hline1 #H1 #Hline2 #H2 #H
      >aux_read_back1 @eq_f2
      [ cut (aux_read_back (val_to_term (pvar ν(S m)))
             (concat (push e1 [νm←b1]) (push e [ν(S m)←b])) =
             aux_read_back (val_to_term (pvar ν(S m)))
              (push e [ν(S m)←b]))
        [2: #UU >UU >push_lemma
            whd in match (match [ν?←b] in Substitution 
              return λ_:Substitution.pifSubst with[_⇒ ?]);
            >atomic_subst >H1 //
            @(transitive_le … (le_maxl … H) Hsn)
        | @ultra_concat_lemma
          <(fresh_var_push)
          normalize
          change with (max ? (max (S m) ?)≤ S m) in ⊢ %;
          @to_max
          [ @(le_S … (transitive_le … (le_maxr … (Hline2 (le_maxr … H))) Hnm))
          | @to_max //
            @(le_S … (transitive_le … (le_maxl … (Hline2 (le_maxr … H))) Hnm))
          ]
        ]
      | cut (aux_read_back (val_to_term (pvar νm))
            (concat (push e1 [νm←b1]) (push e [ν(S m)←b])) =
            aux_read_back (val_to_term (pvar νm))
            (push e1 [νm←b1]))
        [ 2: #UU >UU >push_lemma
             whd in match (match [ν?←b] in Substitution 
              return λ_:Substitution.pifSubst with[_⇒ ?]);
             >atomic_subst @H2 @(le_maxr … H)
        ] @(iper_concat_lemma m n …)
          [ @(le_maxr … (Hline1 (transitive_le … (le_maxl … H) Hsn)))
          | @(le_maxl … (Hline1 (transitive_le … (le_maxl … H) Hsn)))
          | @(le_maxr … (Hline2 (le_maxr … H)))
          | @(le_maxl … (Hline2 (le_maxr … H)))
          | @Hdome
          | @Hnm
          ]
       ]
     ]
   ]
  | * #x #s //
  | #t * #x #HI #s #H cut (fresh_var_t t ≤ s)
    [ lapply H normalize
      change with (fresh_var_t t)
        in match (pi1 nat ? ?);
      change with (max (S x) (fresh_var_t t)) in match (if ? then ? else ?);
      #Htop @(le_maxr … Htop)
    | #H' lapply (HI … H') normalize
      cases ((underline_pifTerm t s)) * #b #e #n normalize
      #Hue >Hue //
    ]
  ] qed.