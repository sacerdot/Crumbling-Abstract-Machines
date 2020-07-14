include "underline_readback.ma".

lemma size_lemma:
 (∀t.∀n. c_size (fst  … (underline_pifTerm t n)) ≤ 5 * (t_size t)) ∧
   (∀v.∀n. c_size_v (fst … (overline v n)) ≤ 5 * (v_size v)).

@pifValueTerm_ind
[ #v #H #s normalize lapply (H s) cases (overline v s) #w #n normalize //
| #t1 #t2 cases t2
  [ #v2 cases t1
    [ #v1 normalize #H1 #H2 #s lapply (H1 s) cases (overline v1 s) #vv #n normalize
      #H1' lapply (H2 (s+n)) cases (overline v2 (s+n)) #ww #m normalize #H2'
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
      change with (underline_pifTerm (appl u1 u2) s) in match (match u2 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
              [val_to_term (v20:pifValue)⇒
               match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
               [val_to_term (v1:pifValue)⇒
                let 〈vv,n0〉 ≝overline v1 s in 
                let 〈ww,m〉 ≝overline v20 (s+n0) in 〈〈AppValue vv ww,Epsilon〉,m+n0〉
               |appl (u10:pifTerm)   (u20:pifTerm)⇒
                let 〈c,n0〉 ≝underline_pifTerm u1 s in 
                match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                [CCrumble (b:Byte)   (e:Environment)⇒
                 let 〈vv,m〉 ≝overline v20 (s+n0) in 
                 〈〈AppValue (var ν(s+n0+m)) vv,push e [ν(s+n0+m)←b]〉,S (s+n0+m)〉]]
              |appl (u10:pifTerm)   (u20:pifTerm)⇒
               let 〈c,n0〉 ≝underline_pifTerm u2 s in 
               match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
               [CCrumble (b1:Byte)   (e1:Environment)⇒
                match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                [val_to_term (v1:pifValue)⇒
                 let 〈vv,m〉 ≝overline v1 (s+n0) in 
                 〈〈AppValue vv (var ν(s+n0+m)),push e1 [ν(s+n0)←b1]〉,S n0〉
                |appl (u100:pifTerm)   (u200:pifTerm)⇒
                 let 〈c1,n1〉 ≝underline_pifTerm u1 (s+n0) in 
                 match c1 in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                 [CCrumble (b:Byte)   (e:Environment)⇒
                  〈〈AppValue (var ν(s+n0+n1)) (var ν(S (s+n0+n1))),
                   concat (push e1 [ν(s+n0+n1)←b1]) (push e [ν(S (s+n0+n1))←b])〉,
                  S (S (s+n0+n1))〉]]]]);
     cases (underline_pifTerm (appl u1 u2) s)
      * #b #e #n normalize lapply (H2 (s+n)) cases (overline v2 (s+n)) #vv #mm
      normalize #H2' #H1' <(size_env_push e  [ν(s+n+mm)←b])
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
    change with (underline_pifTerm (appl u1 u2) ?) in match (match u2 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
              [val_to_term (v2:pifValue)⇒
               match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
               [val_to_term (v1:pifValue)⇒
                let 〈vv,n0〉 ≝overline v1 s in 
                let 〈ww,m〉 ≝overline v2 (s+n0) in 〈〈AppValue vv ww,Epsilon〉,m+n0〉
               |appl (u10:pifTerm)   (u20:pifTerm)⇒
                let 〈c,n0〉 ≝underline_pifTerm u1 s in 
                match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                [CCrumble (b:Byte)   (e:Environment)⇒
                 let 〈vv,m〉 ≝overline v2 (s+n0) in 
                 〈〈AppValue (var ν(s+n0+m)) vv,push e [ν(s+n0+m)←b]〉,S (s+n0+m)〉]]
              |appl (u10:pifTerm)   (u20:pifTerm)⇒
               let 〈c,n0〉 ≝underline_pifTerm u2 s in 
               match c in Crumble return λ_:Crumble.(Crumble×ℕ) with 
               [CCrumble (b1:Byte)   (e1:Environment)⇒
                match u1 in pifTerm return λ_:pifTerm.(Crumble×ℕ) with 
                [val_to_term (v1:pifValue)⇒
                 let 〈vv,m〉 ≝overline v1 (s+n0) in 
                 〈〈AppValue vv (var ν(s+n0+m)),push e1 [ν(s+n0)←b1]〉,S n0〉
                |appl (u100:pifTerm)   (u200:pifTerm)⇒
                 let 〈c1,n1〉 ≝underline_pifTerm u1 (s+n0) in 
                 match c1 in Crumble return λ_:Crumble.(Crumble×ℕ) with 
                 [CCrumble (b:Byte)   (e:Environment)⇒
                  〈〈AppValue (var ν(s+n0+n1)) (var ν(S (s+n0+n1))),
                   concat (push e1 [ν(s+n0+n1)←b1]) (push e [ν(S (s+n0+n1))←b])〉,
                  S (S (s+n0+n1))〉]]]]);
    cases (underline_pifTerm (appl u1 u2) s) * #b #e #n normalize
    lapply (H1 (s+n)) cases t1
    [ #v1 normalize cases (overline v1 (s+n)) #vv #m normalize
      <(size_env_push e  [ν(s+n)←b])
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
  | #r1 #r2 cases (underline_pifTerm (appl r1 r2) (s+n)) * #b1 #e1 #n1 normalize
    >(size_env_concat  (push e [ν(s+n+n1)←b]) (push e1 [ν(S (s+n+n1))←b1]))
    <(size_env_push e  [ν(s+n+n1)←b])
    <(size_env_push e1 [ν(S(s+n+n1))←b1])
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
