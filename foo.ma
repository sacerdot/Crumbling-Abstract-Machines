include "underline_readback.ma".

(*
lemma pif_subst_fv_lemma: 
 (∀t.∀x.∀t'.∀y. fvb_t y (pif_subst (t) (psubst x t')) = ((fvb_t x t) ∧ (fvb_t y t') ∨ (fvb_t y t) ∧ ¬(veqb x y))) ∧ 
  (∀v. ∀x. ∀t'.∀y. fvb_t y (pif_subst_v v (psubst x t')) = ((fvb_tv x v) ∧ (fvb_t y t') ∨ (fvb_tv y v)∧ ¬(veqb x y))).

  
@pifValueTerm_ind
[ #pV #H assumption 
| #t1 #t2 #H1 #H2 #x #t' #y normalize @foo #z #z_def #z_prop lapply(H1 x t' y)  >(H2 x t' y) cases (fvb_t y t2) cases (fvb_t y t1) cases (fvb_t y t') cases (fvb_t x t1) cases (fvb_t x t2) cases (veqb x y) normalize //
| #z #x #t' #y cut (veqb x z=true ∨ veqb x z=false) // cut (veqb y z=true ∨ veqb y z=false) // * #H1 * #H2  
   [ lapply(veqb_true_to_eq … x z) * #Heq #_ lapply (Heq H2) -Heq #Heq destruct
     >H2 -H2 lapply (veqb_true_to_eq y z) * #Heq #_ lapply (Heq H1) -Heq #Heq
     destruct normalize >H1 normalize cases (fvb_t z t') //
   | normalize >H2 lapply(veqb_true_to_eq … y z) * #Heq #_ lapply (Heq H1) -Heq #Heq destruct >H1
     normalize >H2 normalize assumption
   | lapply(veqb_true_to_eq … x z) * #Heq #_ lapply (Heq H2) -Heq #Heq destruct
   normalize >H2 normalize >H1 normalize cases (fvb_t y t') //
   | cut (veqb x y = true ∨ veqb x y =false) // * #H3
     [ lapply (veqb_true_to_eq … x y) * #Heq #_ lapply (Heq H3) -Heq #Heq destruct
     normalize >H2 >H3 normalize assumption
     | normalize >H1 >H2 >H3 normalize assumption
   ]
   ]
| #t #z #H1 #x #t' #y normalize cut (veqb x z = true ∨ veqb x z= false) // * #Hxz
  >Hxz normalize  cut (veqb x y = true ∨ veqb x y= false) // * #Hxy >Hxy normalize
  [ lapply (veqb_true_to_eq … x y) * #Heq #_ lapply (Heq Hxy) -Heq #Heq destruct
    lapply (veqb_true_to_eq … y z) * #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct
    >Hxz normalize //
  | lapply (veqb_true_to_eq … x z) * #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct
    >(veqb_simm y z) >Hxy normalize cases (fvb_t y t) //
  | lapply (veqb_true_to_eq … x y) * #Heq #_ lapply (Heq Hxy) -Heq #Heq destruct
    >Hxz normalize cut (fvb_t z t =true ∨ fvb_t z t=false) // * #Hfvzt >Hfvzt
    normalize


lemma fv_lemma: 
 (∀c.∀x. fvb x c = fvb_t x (read_back c)) ∧
  (∀b.∀x. fvb_b x b = fvb_t x (read_back_b b)) ∧
   (∀e.∀b.∀x. fvb_b x b = fvb_t x (read_back_b b) → fvb x 〈b, e〉 = fvb_t x (read_back 〈b,e〉)) ∧
    (∀v.∀x. fvb_v x v = fvb_t x (read_back_v v)) ∧
     (∀s.∀b.∀e.∀x. fvb_b x b = fvb_t x (read_back_b b) →  fvb x 〈b, (Cons e s)〉 = fvb_t x (read_back 〈b, (Cons e s)〉)).

@Crumble_mutual_ind
[ #b #e #H1 #H2 #x lapply (H1 x) lapply (H2 b x) /2/
| #v #H normalize assumption
| #v #w #H1 #H2 #x normalize >(H1 x) >(H2 x) //
| #x #y normalize //
| #x #c cases c #b #e normalize #H #y lapply (H y) >(veqb_comm y x) elim (veqb x y) normalize
 [ #Hinutile  // | #Hutile @Hutile] 
| #b #x normalize #H <H cases (fvb_b x b) //  
| #e #s #H1 #H2 #b #x #H3 @(H2 b e x) //
| #x #b #H #b' #e #y #H1  normalize cases e normalize cases (read_back_b b')
 [ #v
 


lemma fesh_lemma:
 (∀c. fresh_var c = fresh_var_t (read_back c)) ∧
  (∀b. fresh_var_b b = fresh_var_t (read_back_b b)) ∧
   (∀e.∀b. fresh_var 〈b, e〉 = fresh_var_t (read_back 〈b,e〉)) ∧
    (∀v. fresh_var_v v = fresh_var_t (read_back_v v)) ∧
     (∀s.∀b.∀e. fresh_var 〈b, (Cons e s)〉 = fresh_var_t (read_back 〈b, (Cons e s)〉)).

@Crumble_mutual_ind
[ #b #e #H1 #H2 lapply (H2 b) -H2 #H2 assumption
| #v #H normalize assumption
| #v #w #H1 #H2 normalize change with (max ? ?) in match  (if ? then ? else ?) in ⊢ % ;
  change with (max ? ?) in match (if leb (fresh_var_t (read_back_v v)) (fresh_var_t (read_back_v w))  then ? else ? ) in ⊢%;
  >H1 >H2 //
| #x normalize //
| #x #c elim x #nx cases c #b #e normalize change with (max ? ?) in match  ( if leb (fresh_var_b b) (fresh_var_e e)  then ? else ?) in ⊢ % ;
  #H >H //
| #b normalize change with (max ? ?) in match  ( if ? then ? else ?) in ⊢ %; >max_O
 [ #v normalize cases v
  [ #x normalize //
  | #x #c elim x #nx cases c #b #e normalize change with (max ? ?) in match  ( if leb ? ? then ? else ?) in ⊢ %;
  
   #s #H1 #H2 #b @ (H2 b e)
| #x #b #H #b #e normalize 
 #b normalize cases b
 [#v normalize change with (max ? ?) in match  ( if ? then ? else ?) in ⊢ %; >max_O cases v #x normalize //
  #c elim x #nx normalize cases c #b #e change with (max ? ?) in match  ( if leb (fresh_var_b b) (fresh_var_e e)  then ? else ?) in ⊢ % ;
  normalize
  change with (fresh_var_v (lambda (ν?) 〈?, ? 〉)) in match  ( if ? then ? else ?) in ⊢ %;
  change with (fresh_var_tv (abstr (ν?) 〈?, ? 〉)) in match  ( if ? then ? else ?) in ⊢ %;
  case
*)

     
lemma value_lemma:
  ∀v: pifValue. ∀ n. n ≥ fresh_var_tv v →
  match (overline v n) with
   [ mk_Prod v' m ⇒ (read_back_v v') = (val_to_term v) ∧ (m + n ≥ (fresh_var_v v')) ].

#v @(pifValue_ind … v)
[ @(λt. ∀n. n ≥ fresh_var_t t →
  match (underline_pifTerm t n) with
  [ mk_Prod c m ⇒ read_back c = t ∧ m+n ≥ fresh_var c])
| #v0 cases v0 (*devo dimostrare per ogni v0*)
 [#x elim x #nx normalize /2/
 | #x elim x #nx #t normalize #HI #m lapply (HI m ) cases (underline_pifTerm t m)
   * #b #e #fv_c -HI @foo #z #z_def #z_prop
   whd in ⊢ ((? → %) → ? → %);
   #H #H1 lapply (H H1) -H -H1 * #H2 #H3
   whd in ⊢ (? (??%?) (?%?));
   whd in H2:(??%?);
   whd in H3:(?%?);
   % // whd in match (fresh_var_b ?);
   whd in match (fresh_var_e Epsilon);
   /2/
   ]
| #t1 #t2 cases t2
 [ #v2 cases t1
  [ #v1 normalize #H1 #H2 #n lapply (H1 n) cases (overline v1 n) #vv #m lapply (H2 (n+m)) normalize
    cases (overline v2 (n+m)) #ww #mm normalize
    change with (max ? ?) in match  (if ? then ? else ?) in ⊢ % ;
    change with (max ? ?) in match  (if leb (fresh_var_v vv) (fresh_var_v ww)  then ? else ?) in ⊢ % ;
    change with (max ? ?) in match  (if leb (max (fresh_var_v vv) (fresh_var_v ww)) O then ? else ?)  in ⊢ % ;
    >max_O >max_O
    @foo #z #z_def #z_prop #Hz
    @foo #y #y_def #y_prop #Hy
    change with (max ? ?) in match  (if ? then ? else ?) in Hy ;
    >max_O in Hy;
    #Hy change with (max ? ?) in match  (if ? then ? else ?) in ⊢ % ;
    #Hmax lapply (le_maxl … Hmax) #Hyhead lapply (le_maxr … Hmax) #Hzhead
    cut (z≤n+m) /2/ -Hzhead #Hzhead lapply(Hz Hzhead) * -Hz -Hzhead #Hz1 #Hz2
    lapply(Hy Hyhead) * -Hy -Hyhead #Hy1 #Hy2 %
    [ >Hz1 >Hy1 // | normalize cases (leb (fresh_var_v vv) (fresh_var_v ww))
      normalize /2/]
  | #u1 #u2 #H1 #H2 #n
    change with (max ??) in ⊢ (??% → ?);
    @foo #fv1 #fv1_def #fv1_prop
    @foo #fv2 #fv2_def #fv2_prop
    #HMAX
    whd in match (underline_pifTerm ??);
    lapply (H1 n) -H1
    cases (underline_pifTerm (appl u1 u2) n)
    #c #m lapply (H2 (m + n)) -H2
    cases (underline_pifTerm (val_to_term v2) (m+n))
    #c2 #m2
    cases c #b #e whd in ⊢ ((? → %) → (? → %) → %);
    #H2 #H1 normalize
    cases (overline v2 (n+m)) (* perdita di info *)
    #vv #mm whd
  
(*=============================*)
XXX
  
   #u1 #u2  #H1 #H2 #n lapply (H1 n) whd in match (underline_pifTerm ? ?) in ⊢ (? → %); -H1 cases (underline_pifTerm (appl u1 u2) n)
#c #m normalize lapply (H2 (n+m)) cases (overline v2 (n+m)) #vv #mm
change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
change with (max ? ?) in match (if leb (max ? ?) ? then ? else ?) in ⊢ %; -H2
@foo #z #z_def #z_prop
@foo #y #y_def #y_prop
@foo #w #w_def #w_prop #H2 #H1 #H3
change with (fresh_var_t (appl ? ?)) in match (max (fresh_var_t ?) (fresh_var_t ?)) in H3;
change with (fresh_var_t (val_to_term ?)) in match (fresh_var_tv ?) in H3;
change with (fresh_var_t (appl ? ?)) in match (max (fresh_var_t ?) ?) in H3;
lapply H1 cases c #b #e -H1 #H1 whd in ⊢ %;
whd in match (read_back ?) ; % [ | lapply (le_maxl … H3) #H4 lapply (le_maxr … H3) -H3
lapply (H1 H4) -H1 #H1 #H3 lapply(le_maxl … H4) #H5 lapply(le_maxr … H4) -H4 #H4
lapply H1 * #_ -H1 #H1 normalize
change with (leb (S ?) ?) in match (match fresh_var_v vv in nat return λ_:ℕ.bool with 
             [O⇒false|S (q:ℕ)⇒leb (n+m+mm) q]) in ⊢ %;
change with (max ? ?) in match  (if ? then ? else ?) in ⊢ % ;
    change with (max ? ?) in match (if leb (S (n+m+mm)) (fresh_var_v vv) then fresh_var_v vv else S (n+m+mm)) in ⊢ % ;
 normalize
change with (max ? ?) in match  (if ? then ? else ?) in ⊢ % ;
change with (?) in match (match fresh_var_v vv in nat return λ_:ℕ.bool with 
         [O⇒false|S (q:ℕ)⇒leb (n+m+mm) q]) in ⊢ %;
 cases (fresh_var_v vv) normalize

lemma term_lemma:
 ∀t: pifTerm. ∀n. n= fresh_var_t t →
  match (underline_pifTerm t n) with
  [ mk_Prod c m ⇒ read_back c = t ∧ m+n=fresh_var c].
#t @(pifTerm_ind … t)
[ @(λv.∀ n. n = fresh_var_tv v →
  match (overline v n) with
   [ mk_Prod v' m ⇒ (read_back_v v') = (val_to_term v) ∧ (m + n = (fresh_var_v v')) ])
| (*#v cases v [ #x  #Hv normalize cases x #nx normalize /2/
 | #x #t1 elim x #nx normalize cases (fresh_var_t t1)
  [ normalize #H #n #Hn cases (underline_pifTerm t1 n) #c #m normalize*)
| #t1 #t2 #Hind1 #Hind2 #n #Hn cases (underline_pifTerm (appl t1 t2)) #c #m
 normalize