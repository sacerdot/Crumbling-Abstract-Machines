include "crumbles.ma".
include "basics/types.ma".
include "libnat.ma".
include "variables.ma".
include "utils.ma".
include "size.ma".

lemma pif_subst_aux1: (∀t. S (t_size t -1)=t_size t) ∧ (∀v. S (v_size v -1)=v_size v).
@pifValueTerm_ind
[ #v #H normalize //
| #t1 #t2 #H1 #H2 normalize //
| #x normalize //
| #t #x #H normalize //]
qed.

(*
lemma generalize_sigma_prop_gen:
 ∀n,s,p,P.
  (∀q. P (pif_subst n s t q)) →
    P (pif_subst n s t p).
*)

lemma subst_aux_1:
 ∀ y, t', t.
  t_size t≤O
     →Σu:pifTerm
      .t_size u
       =t_size t
        +free_occ_t y t
         *(t_size t' -1)
       ∧(∀z:Variable
         .free_occ_t z u
          =if veqb y z 
           then free_occ_t z t
                    *free_occ_t z t'
           else free_occ_t y t
                    *free_occ_t z t'
                    +free_occ_t z t ).

#y #t' #t
cases t
  [ #v cases v
    [ #x normalize #Abs lapply (leq_zero 0 Abs) -Abs #Abs elim Abs
    | #x #t normalize #Abs lapply (leq_zero (t_size t) Abs) -Abs #Abs elim Abs
    ]
  | #t1 #t2 normalize #Abs lapply (leq_zero ((t_size t1)+(t_size t2)) Abs) -Abs #Abs elim Abs
  ]
qed.


lemma subst_aux_2:
 ∀ t',x, y, m.
  (veqb y x=true) →
   (t_size (val_to_term (pvar x))≤S m) →
 (And ((t_size t')
  =t_size (val_to_term (pvar x))
   +free_occ_v y(pvar x)
    *(t_size t' -1))
  (∀z:Variable
    .free_occ_t z t'
     =if veqb y z 
      then free_occ_v z (pvar x)
               *free_occ_t z t'
      else free_occ_v y
               (pvar x)
               *free_occ_t z t'
               +free_occ_v z (pvar x) )).

#t' #x #y #m #H #p
normalize in p; normalize >H normalize <(plus_n_O (t_size t' -1))
lapply(pif_subst_aux1) * #H1 #_ >(H1 t') % //
#z lapply (veqb_true_to_eq y x) * #H' #_ lapply (H' H) -H -H' #H destruct
cut (veqb x z =veqb z x)
[ @(veqb_comm …)
| cut (veqb x z =true ∨ veqb x z =false) // * #Hxz
  #Heq <Heq >Hxz normalize //
]
qed.

lemma subst_aux_3:
 ∀ t',x, y, m.
  (veqb y x=false) →
   (t_size (val_to_term (pvar x))≤S m) →
 (t_size (val_to_term (pvar x))
  =t_size (val_to_term (pvar x))
   +free_occ_v y (pvar x)
    *(t_size t'-1)
  ∧(∀z:Variable
    .free_occ_t z (val_to_term (pvar x))
     =if veqb y z 
      then free_occ_v z (pvar x)
               *free_occ_t z t'
      else free_occ_v y
               (pvar x)
               *free_occ_t z t'
               +free_occ_v z (pvar x) )).

#t' #x #y #m #H #p

normalize normalize >H normalize in p; normalize % // #z
  cut (veqb z x = true ∨ veqb z x = false) // * #Hzx
   [ lapply (veqb_true_to_eq z x) * #Heq #_
    lapply (Heq Hzx) -Heq #Heq destruct >H
   >(veqb_true x) normalize //
   | cut (veqb y z = true ∨ veqb y z = false) // * #Hyz
     lapply (veqb_true_to_eq y z) * #Heq #_
      [ lapply (Heq Hyz) -Heq #Heq destruct >Hzx >Hyz normalize //
      | >Hzx >Hyz normalize //
      ]
   ]

qed.

lemma subst_aux_4:
 ∀ t1,x,y,t', m.
   (veqb y x = true) →
    (t_size (val_to_term (abstr x t1))≤S m)→
     (t_size (val_to_term (abstr x t1))
      = t_size (val_to_term (abstr x t1))
        +(free_occ_v y (abstr x t1))
        *(t_size t'-1)
  ∧(∀z:Variable
    .free_occ_t z (val_to_term (abstr x t1))
     =if veqb y z 
      then free_occ_v z (abstr x t1)
               *(free_occ_t z t') 
      else free_occ_v y (abstr x t1)
               *(free_occ_t z t')
               +free_occ_v z (abstr x t1) )).

#t1 #x #y #t' #m #H #_

lapply H normalize #H1 >H1 normalize % //
  lapply (veqb_true_to_eq y x) * #Heq #_ lapply (Heq H1) -Heq #Heq destruct
  #z lapply (veqb_comm x z) #Hcomm >Hcomm -Hcomm cases (veqb z x) normalize //

qed.

lemma subst_aux_5: ∀t1, x, z, a, m.

(t_size a
   =t_size t1
    +free_occ_t
     match psubst x (val_to_term (pvar νz))
      in pifSubst
      return λ_:pifSubst.Variable
      with 
     [psubst (x0:Variable)   (t0:pifTerm)⇒x0] t1
     *(t_size
       match psubst x (val_to_term (pvar νz))
        in pifSubst
        return λ_:pifSubst.pifTerm
        with 
       [psubst (x0:Variable)   (t0:pifTerm)⇒t0]
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 a
      =if veqb
            match psubst x (val_to_term (pvar νz))
             in pifSubst
             return λ_:pifSubst.Variable
             with 
            [psubst (y:Variable)   (t':pifTerm)⇒y] z0 
       then free_occ_t z0 t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar νz))
                  in pifSubst
                  return λ_:pifSubst.pifTerm
                  with 
                 [psubst (y:Variable)   (t':pifTerm)⇒t'] 
       else free_occ_t
                match psubst x (val_to_term (pvar νz))
                 in pifSubst
                 return λ_:pifSubst.Variable
                 with 
                [psubst (y:Variable)   (t':pifTerm)⇒y] t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar νz))
                  in pifSubst
                  return λ_:pifSubst.pifTerm
                  with 
                 [psubst (y:Variable)   (t':pifTerm)⇒t']
                +free_occ_t z0 t1 )) →
                (t_size (val_to_term (abstr x t1))≤S m) →
                t_size a ≤ m.

#t1 #x #z #a #m #h #p
normalize in h; lapply h * -h #h #_ normalize in p; /2/
qed.

lemma pif_subst_aux_6:
∀( n : ℕ).
∀( y : Variable).
∀( t' : pifTerm).
∀( m : ℕ).
∀( t : pifTerm).
∀( v : pifValue).
∀( x : Variable).
∀( t1 : pifTerm).
∀( H : (veqb y x = false)).
∀( HH : (fvb_t x t' = true)).
∀( p : (t_size (val_to_term (abstr x t1))≤S m)).
∀( z : ℕ).
∀( hz: z =
  (max
   (S match y in Variable return λ_:Variable.ℕ with [variable (n0:ℕ)⇒n0])
   (max (S match x in Variable return λ_:Variable.ℕ with [variable (nx:ℕ)⇒nx])
    (max (fresh_var_t t1)
     (fresh_var_t t'))))).
∀( a : pifTerm).
∀( h :
  (t_size a
   =t_size t1
    +free_occ_t
     match psubst x (val_to_term (pvar (νz)))
      in pifSubst
      return λ_:pifSubst.Variable
      with 
     [psubst (x0:Variable)   (t0:pifTerm)⇒x0] t1
     *(t_size
       match psubst x (val_to_term (pvar νz))
        in pifSubst
        return λ_:pifSubst.pifTerm
        with 
       [psubst (x0:Variable)   (t0:pifTerm)⇒t0]
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 a
      =if veqb
            match psubst x (val_to_term (pvar (νz)))
             in pifSubst
             return λ_:pifSubst.Variable
             with 
            [psubst (y:Variable)   (t':pifTerm)⇒y] z0 
       then free_occ_t z0 t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar (νz)))
                  in pifSubst
                  return λ_:pifSubst.pifTerm
                  with 
                 [psubst (y:Variable)   (t':pifTerm)⇒t'] 
       else free_occ_t
                match psubst x (val_to_term (pvar (νz)))
                 in pifSubst
                 return λ_:pifSubst.Variable
                 with 
                [psubst (y:Variable)   (t':pifTerm)⇒y] t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar (νz)))
                  in pifSubst
                  return λ_:pifSubst.pifTerm
                  with 
                 [psubst (y:Variable)   (t':pifTerm)⇒t']
                +free_occ_t z0 t1 ))).
∀( k : pifTerm ).
∀( k_size :
  (t_size k
   =t_size a
    +free_occ_t y a
     *(t_size t'-1)
   ∧(∀z00:Variable
     .free_occ_t z00 k
      =if veqb y z00 
       then free_occ_t z00 a
                *free_occ_t z00 t' 
       else free_occ_t y a
                *free_occ_t z00 t'
                +free_occ_t z00 a ))).

 (t_size (val_to_term (abstr (νz) k))
  =t_size (val_to_term (abstr x t1))
   +free_occ_v y (abstr x t1)
    *(t_size t' -1)
  ∧(∀z00:Variable
    .free_occ_t z00 (val_to_term (abstr (νz) k))
     =if veqb y z00 
      then free_occ_v z00 (abstr x t1)
               *free_occ_t z00 t' 
      else free_occ_v y (abstr x t1)
               *free_occ_t z00 t'
               +free_occ_v z00 (abstr x t1) )).
#n #y #t' #m #t #v #x #t1 #H #HH #p #z #z_def #a #h #k #k_size destruct

whd in match (t_size ?) in ⊢ %;
  whd in match (t_size (val_to_term ?)) in ⊢ %;
  lapply k_size * -k_size #k_size #k_fv >k_size lapply h -h * #a_size #a_fv >a_size lapply H
   normalize in a_fv; lapply a_fv lapply k_fv normalize -k_fv #k_fv normalize
  -H normalize -a_fv #a_fv #H >H normalize lapply (a_fv y) normalize lapply (veqb_comm x y)
  #Hcomm >Hcomm >H normalize change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
  lapply a_fv lapply k_fv
  lapply H
  elim y #ny
  -H #H
  #k_fv_ny #a_fv_ny normalize change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
  change with (leb (S ?) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb ny q]);
  change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
  >(neqb_x_max_Sx ny ?) whd in match (if false then 1 else O); #Hfva >Hfva % [ /2/
  | #ww lapply k_fv_ny lapply (a_fv_ny ww) normalize
    -k_fv_ny -a_fv_ny #a_fv_ny #k_fv_ny >(k_fv_ny ww) lapply (a_fv_ny) elim ww #nww
    lapply H elim x #nx -H normalize #H
    change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
    change with (leb (S ?) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb ny q]);
    change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
    -a_fv_ny #a_fv_ny >a_fv_ny
    cut (neqb nww nx = true ∨ neqb nww nx=false) // * #Hzx lapply (neqb_iff_eq nww nx) *
    #Heq #_
    change with (fresh_var_t t1) in match (pi1 ℕ (λn0:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t1→S x0≤n0)
                   (fresh_var_t_Sig t1));
    change with (fresh_var_t t') in match (pi1 ℕ (λn0:ℕ.∀x0:ℕ.1≤free_occ_t (νx0) t'→S x0≤n0)
                   (fresh_var_t_Sig t'));
    [ lapply (Heq Hzx) -Heq #Heq destruct >(rifle_neqb … nx) normalize
      cut (neqb nx ny = true ∨neqb nx ny = false) // * #Hxy lapply (neqb_iff_eq nx ny) *
      #Heq2 #_
      [ lapply (Heq2 Hxy) -Heq2 #Heq2 destruct >Hxy >(rifle_neqb … ny) normalize
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ny) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t') in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb ny q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match (match max (S ny) (max (fresh_var_t t1) (fresh_var_t t'))
              in nat with 
             [O⇒false|S (q:ℕ)⇒leb ny q] );
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        >(neqb_x_max_Sx … ny (max (S ny) (max (fresh_var_t t1) (fresh_var_t t')))) normalize /2/
      | -Heq2 >(neq_simm ny nx) >Hxy
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S nx) ?) in match (match max (fresh_var_t t1) (fresh_var_t t')
                                         in nat with [_⇒?]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match (match max (S nx) (max (fresh_var_t t1) (fresh_var_t t'))
                                    in nat with [_⇒ ?]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        cut ( neqb nx (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t')))) = false)
        [ /2/ | #Hfalse >Hfalse normalize >Hfva /2/]
      ]
    | -Heq cut (neqb ny nww =true ∨ neqb ny nww = false) // * #Hyz >Hyz
      [ lapply (neqb_iff_eq ny nww) * #Heq #_ lapply (Heq Hyz) -Heq #Heq
        destruct >if_t >if_t
        change with (leb (S nx) ?) in match (match max (fresh_var_t t1) (fresh_var_t t')
                                         in nat with [_⇒?]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match (match max (S nx) (max (fresh_var_t t1) (fresh_var_t t'))
                                    in nat with [_⇒ ?]);
        change with (leb (S ?) ?) in match ( match  max (S nx) (max (fresh_var_t t1) (fresh_var_t t)) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb nww q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        cut (  neqb nww (max (S nww) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t')))) = false)
        [/2/ | #Hfalse >Hfalse >if_f >if_f >(neq_simm nx nww) >Hzx >if_f >if_f /2/]
      | lapply H -H #Hxy >(neq_simm ny nx) >(neq_simm nww ny) >(neq_simm nx nww) >Hxy >Hyz >Hzx
          change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
          change with (leb (S nx) ?) in match (match max (fresh_var_t t1) (fresh_var_t t')
                                         in nat with [_⇒?]);
          change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
          change with (leb (S ?) ?) in match (match max (S nx) (max (fresh_var_t t1) (fresh_var_t t'))
                                    in nat with [_⇒ ?]);
          change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
          cut ( neqb nww (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t')))) =true ∨ neqb nww (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t'))))=false)
          // * #Htf
          [ >Htf >if_t >if_f >if_f lapply (neqb_iff_eq nww (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t')))))
            * #Heq #_ lapply (Heq Htf) -Heq -Htf #Heq >Heq normalize
            change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
            change with (leb (S nx) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t') in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb nx q]);
             change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
             change with (leb (S ?) ?) in match ( match  max (S nx) (max (fresh_var_t t1) (fresh_var_t t')) in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb ny q]);
             change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
             >(max_comm (fresh_var_t t1) (fresh_var_t t)) in match ((free_occ_t (νny) t1)*free_occ_t (ν(max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t))))) t);
             >(max_swap (S nx) (fresh_var_t t') (fresh_var_t t1))
             >(max_swap (S ny) (fresh_var_t t') (max (S nx) (fresh_var_t t1)))
             >(max_swap (S nx) (fresh_var_t t1) (fresh_var_t t'))
             >(max_swap (S ny) (fresh_var_t t1) (max (S nx) (fresh_var_t t')))
             /2/ |>Hfva >Htf normalize /2/
          ]
      ]
    ]
  ]
qed.

lemma subst_aux_7: ∀x, t1, m. (t_size (val_to_term (abstr x t1))≤S m) → (t_size t1)≤ m.
#x #t1 #m #p normalize in p; /2/
qed.

lemma subst_aux_8:
∀( y : Variable).
∀( t' : pifTerm).
∀( m : ℕ).
∀( x : Variable).
∀( t1 : pifTerm).
∀( H :
  (veqb y x
   =false)).
∀( HH :
  (fvb_t x t'  =false)).
∀( p : (t_size (val_to_term (abstr x t1))≤S m)).
∀( k : pifTerm).

 (t_size k
  =t_size t1
   +free_occ_t y t1
    *(t_size t' -1)
  ∧(∀z0:Variable
    .free_occ_t z0 k
     =if veqb y z0 
      then free_occ_t z0 t1
               *free_occ_t z0 t'
      else free_occ_t y t1
               *free_occ_t z0 t'
               +free_occ_t z0 t1 )
  →t_size (val_to_term (abstr x k))
   =t_size (val_to_term (abstr x t1))
    +free_occ_v y (abstr x t1)
     *(t_size t'
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 (val_to_term (abstr x k))
      =if veqb y z0 
       then free_occ_v z0 (abstr x t1)
                *free_occ_t z0 t'
       else free_occ_v y (abstr x t1)
                *free_occ_t z0 t'
                +free_occ_v z0 (abstr x t1) )).

#y #t' #m #x #t1 #H #HH #p #k

lapply HH lapply H 
  -H #H -HH #HH lapply (gtb_O (free_occ_t x t')) normalize in HH;
  lapply HH -HH #HH #HHH lapply(HHH HH) -HH -HHH #HH * #Hk_size #Hfok
  whd in match (t_size (val_to_term ?));
  whd in match (t_size (val_to_term ?));
  whd in match (free_occ_v y (abstr x t1));
  >H %
  [ >Hk_size normalize //
  | #z normalize cut ( veqb z x = true ∨ veqb z x = false) // * #Hzx >Hzx
    [ normalize lapply (veqb_true_to_eq z x) * #Heq #_ lapply (Heq Hzx)
      -Heq -Hzx #Heq destruct >HH >H normalize //
    | normalize >(Hfok z) //
    ]
  ]
qed.

lemma subst_aux_9:
 ∀t', u, m. t_size (appl t' u)≤S m →
  (t_size u≤m).
#t #p #m normalize /3/ qed.

lemma subst_aux_10:
 ∀t', u, m. t_size (appl t' u)≤S m →
  (t_size t'≤m).
#t #p #m normalize /3/ qed.

lemma subst_aux_11:
∀( n : ℕ).
∀( y : Variable).
∀( t' : pifTerm).
∀( m : ℕ).
∀( t : pifTerm).
∀( t2 : pifTerm).
∀( u : pifTerm).
∀( p: (t_size (appl t2 u)≤S m)).
∀( k : pifTerm).
∀( j : pifTerm ).

 (t_size j=t_size u+free_occ_t y u*(t_size t'-1)
  ∧(∀z0:Variable
    .free_occ_t z0 j
     =if veqb y z0 
      then free_occ_t z0 u*free_occ_t z0 t' 
      else free_occ_t y u*free_occ_t z0 t'+free_occ_t z0 u )
  →t_size k=t_size t2+free_occ_t y t2*(t_size t'-1)
   ∧(∀z0:Variable
     .free_occ_t z0 k
      =if veqb y z0 
       then free_occ_t z0 t2*free_occ_t z0 t' 
       else free_occ_t y t2*free_occ_t z0 t'+free_occ_t z0 t2 )
   →t_size (appl k j)=t_size (appl t2 u)+free_occ_t y (appl t2 u)*(t_size t'-1)
    ∧(∀z0:Variable
      .free_occ_t z0 (appl k j)
       =if veqb y z0 
        then free_occ_t z0 (appl t2 u)*free_occ_t z0 t' 
        else free_occ_t y (appl t2 u)*free_occ_t z0 t'+free_occ_t z0 (appl t2 u) )).

#n #y #t' #m #t #t2 #u #p #k #j
* #Hj_size #Hfoj * #Hk_size #Hfok %
  [ normalize >Hk_size >Hj_size normalize @eq_f
   cases (t_size t') normalize // #n normalize /2/
  | #z normalize >(Hfoj z) >(Hfok z) normalize
    cut (veqb y z= true ∨ veqb y z= false) // * #Hyz >Hyz normalize /2/
  ]
qed.

lemma subst_aux_12:
∀ (y : Variable).
∀ (t' : pifTerm).
∀ (m : ℕ).
∀ (t : pifTerm).
∀ (v : pifValue).
∀ (x : Variable).
∀ (t1 : pifTerm).
∀ (H : (veqb y x=false)).
∀ (HH : (fvb_t x t'=true)).
∀ (Hfv : (fvb_t y (val_to_term (abstr x t1))=false)).
∀ (p : (t_size (val_to_term (abstr x t1))≤S m)).
  
 (t_size (val_to_term (abstr x t1))
  =t_size (val_to_term (abstr x t1))
   +free_occ_t y (val_to_term (abstr x t1))*(t_size t'-1)
  ∧(∀z:Variable
    .free_occ_t z (val_to_term (abstr x t1))
     =if veqb y z 
      then free_occ_t z (val_to_term (abstr x t1))*free_occ_t z t' 
      else free_occ_t y (val_to_term (abstr x t1))*free_occ_t z t'
               +free_occ_t z (val_to_term (abstr x t1)) )).
      
#y #t'#m #t #v #x #t1 #H #HH #Hfv #p

%
[ lapply Hfv normalize >H >if_f -Hfv #Hfv lapply (free_occ_to_fv y) * #H #_ lapply (H t1)
  * #_ -H #H lapply (H Hfv) -H #H >H normalize //
| #z cut (veqb y z =true ∨ veqb y z =false) //
  normalize in Hfv; >H in Hfv; >if_f #Hfv lapply (gtb_O … Hfv) #HH *
  [ #Htf >Htf normalize lapply (veqb_true_to_eq y z) * #Heq #_
    lapply (Heq Htf) -Heq #Heq destruct >H >if_f >HH //
  | #Hyz >Hyz >if_f normalize >H >if_f >HH normalize //
  ]
] qed.

let rec pif_subst_sig (n: nat) y t': Πt. (t_size t ≤ n) →
 Σu: pifTerm. ((t_size u = (t_size t)+ (free_occ_t y t) * (t_size t' - 1) ∧
  (∀z. free_occ_t z u = match veqb y z with
   [ true ⇒ (free_occ_t z t) * (free_occ_t z t')
   | false ⇒ (free_occ_t y t) * (free_occ_t z t') + (free_occ_t z t)
   ]))) ≝
 match n return λn. Πt. (t_size t ≤ n) → Σu: pifTerm. ((t_size u = (t_size t)+ (free_occ_t y t) * ((t_size t') - 1)) ∧
  (∀z. free_occ_t z u = match veqb y z with
   [ true ⇒ (free_occ_t z t) * (free_occ_t z t')
   | false ⇒ (free_occ_t y t) * (free_occ_t z t') + (free_occ_t z t)
   ]))
  with
 [ O ⇒ λt.?
 | S m ⇒ λt. match t return λt.  t_size t ≤ S m → Σu: pifTerm. ((t_size u = (t_size t)+ (free_occ_t y t) * ((t_size t') - 1)) ∧
    (∀z. free_occ_t z u = match veqb y z with
    [ true ⇒ (free_occ_t z t) * (free_occ_t z t')
    | false ⇒ (free_occ_t y t) * (free_occ_t z t') + (free_occ_t z t)
    ]))
   with
    [ val_to_term v ⇒ match v return λv.  t_size (val_to_term v) ≤ S m → Σu: pifTerm. (t_size u = (t_size (val_to_term v))+ (free_occ_v y v) * ((t_size t') - 1) ∧
      (∀z. free_occ_t z u = match veqb y z with
       [ true ⇒ (free_occ_v z v) * (free_occ_t z t')
       | false ⇒ (free_occ_v y v) * (free_occ_t z t') + (free_occ_v z v)
       ]))
      with
     [ pvar x ⇒  match veqb y x return λb.  veqb y x = b → t_size (val_to_term (pvar x)) ≤ S m → Σu: pifTerm. (t_size u = (t_size (val_to_term (pvar x)))+ (free_occ_v (match (psubst y t') with [psubst x t ⇒ x]) (pvar x)) * ((t_size (match (psubst y t') with [psubst x t ⇒ t])) - 1) ∧
        (∀z. free_occ_t z u = match veqb (match (psubst y t') with [psubst y t' ⇒ y]) z with
          [ true ⇒ (free_occ_v z (pvar x)) * (free_occ_t z match (psubst y t') with [psubst y t' ⇒ t'])
          | false ⇒ (free_occ_v (match (psubst y t') with [psubst y t' ⇒ y]) (pvar x)) * (free_occ_t z match (psubst y t') with [psubst y t' ⇒ t']) + (free_occ_v z (pvar x))
          ]))
        with
         [true ⇒λH.λp.mk_Sig … t' ? | false ⇒ λH.λp.mk_Sig … (val_to_term (pvar x)) ?] (refl …)
     | abstr x t1 ⇒ match veqb y x return λb. veqb y x = b → t_size (val_to_term (abstr x t1)) ≤ S m → Σu: pifTerm. (t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_v y (abstr x t1)) * ((t_size t') - 1) ∧
        (∀z. free_occ_t z u = match veqb y z with
          [ true ⇒ (free_occ_v z (abstr x t1)) * (free_occ_t z t')
          | false ⇒ (free_occ_v y (abstr x t1)) * (free_occ_t z t') + (free_occ_v z (abstr x t1))
          ]))
       with
        [ true ⇒ λH.λp. mk_Sig …  (val_to_term (abstr x t1)) ?
        | false ⇒ λH. match fvb_t x t' return λb. fvb_t x t'=b → t_size (val_to_term (abstr x t1)) ≤ S m → Σu: pifTerm. (t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_v y (abstr x t1)) * ((t_size t') - 1) ∧
          (∀z. free_occ_t z u = match veqb y z with
            [ true ⇒ (free_occ_v z (abstr x t1)) * (free_occ_t z t')
            | false ⇒ (free_occ_v (y) (abstr x t1)) * (free_occ_t z t') + (free_occ_v z (abstr x t1))
            ]))
         with
          [ true ⇒ λHH. match fvb_t y (val_to_term (abstr x t1)) return λHfvb. fvb_t y (val_to_term (abstr x t1)) = Hfvb →  t_size (val_to_term (abstr x t1)) ≤ S m → Σu: pifTerm. ((t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_t y (val_to_term (abstr x t1))) * ((t_size t') - 1)) ∧
            (∀z. free_occ_t z u = match veqb y z with
               [ true ⇒ (free_occ_t z (val_to_term (abstr x t1))) * (free_occ_t z t')
               | false ⇒ (free_occ_t y (val_to_term (abstr x t1))) * (free_occ_t z t') + (free_occ_t z (val_to_term (abstr x t1)))
               ]))
             with
            [ true ⇒ λHfv.λp. let z ≝ (max (S match y with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig m x (val_to_term (pvar ν(z))) t1 ?) with
               [ mk_Sig a h ⇒ mk_Sig …  (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig m y t' a ?)))) ?]
            | false ⇒ λHfv. λp. mk_Sig pifTerm ? (val_to_term (abstr x t1)) ?
            ] (refl …)
          | false ⇒ λHH. λp. mk_Sig … (val_to_term (abstr x (pi1 … (pif_subst_sig m y t' t1 ?)))) ?
          ] (refl …)
        ] (refl …)
     ]
    | appl t2 u ⇒  λp. mk_Sig … (appl (pi1 …(pif_subst_sig m y t' t2 ? )) (pi1 … (pif_subst_sig m y t' u ?))) ?
    ]
 ]
.
[ @(subst_aux_1 …)
| @(subst_aux_2 … m H p)
| @(subst_aux_3 … m H p)
| @(subst_aux_4 … m H p)
| @(subst_aux_5 … h p)
| @sigma_prop_gen #k #k_def #k_size @(pif_subst_aux_6 n y t' m t v x t1 H HH p ? ? a h k k_size) //
| 7,9: @(subst_aux_7 … p)
| 10:@sigma_prop_gen #k #_ @(subst_aux_8 y t' m x ? H HH p)
| 11: @(subst_aux_9 … p)
| 12: @(subst_aux_10 t2 u m p)
| 13: @sigma_prop_gen #k #_
  @sigma_prop_gen #j #_ @(subst_aux_11 n y t' m t t2 u p k j)
| 8: @(subst_aux_12 … y t' m t v x t1 H HH Hfv p)
]
qed.

definition pif_subst ≝ λt.λs. pi1 … (pif_subst_sig (t_size t) match s with [psubst y t' ⇒ y] match s with [psubst y t' ⇒ t'] t ?).// qed.
definition pif_subst_v ≝ λv.λs. pi1 … (pif_subst_sig (t_size (val_to_term v)) match s with [psubst y t' ⇒ y] match s with [psubst y t' ⇒ t'] (val_to_term v) ?).// qed.

lemma atomic_subst: ∀x, t. (pif_subst (val_to_term (pvar x)) (psubst x t)) = t.
#x #t change with (pi1 … (pif_subst_sig …)) in match (pif_subst (val_to_term (pvar x)) (psubst x t));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (t_size (val_to_term (pvar x)) );
normalize in match (pif_subst_sig 1 x t (val_to_term (pvar x)));
cut (∀gg.∀ tt. (pi1 pifTerm
  (λu:pifTerm
   .t_size u=1+(free_occ_t x (val_to_term (pvar x)))*((t_size t)-1)
    ∧(∀z:Variable
      .free_occ_t z u
       =if veqb x z 
        then (free_occ_t z (val_to_term (pvar x)))*(free_occ_t z t) 
        else (free_occ_t x (val_to_term (pvar x)))*(free_occ_t z t)
                 +free_occ_t z (val_to_term (pvar x))))
 (match veqb x x
 return λb. veqb x x = b → 1 ≤ 1 →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb x x = true.
        λp: 1 ≤ 1.
         «t, gg H p»
     | false ⇒ λH: veqb x x = false.
        λp: 1 ≤ 1.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb x x )) (le_n 1))) = t)
     [ 2: #gg >(gg …) /3/]
  #gg #tt >(veqb_true …) in gg tt ⊢ %;
  normalize // qed.

lemma no_subst: ∀x, y, t. veqb y x =false → pif_subst (val_to_term (pvar x)) (psubst y t) =val_to_term (pvar x).
#x #y #t #H
change with (pi1 … (pif_subst_sig …)) in match (pif_subst (val_to_term (pvar x)) (psubst y t));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (t_size (val_to_term (pvar x)) );
whd in match (pif_subst_sig 1 y t (val_to_term (pvar x)) (le_n 1));
cut (∀gg.∀ tt. eq pifTerm (pi1 pifTerm
  (λu:pifTerm
   .t_size u=(1+free_occ_t y (val_to_term (pvar x))*(t_size t-1))
    ∧(∀z:Variable
      .free_occ_t z u
       =if veqb y z 
        then (free_occ_t z (val_to_term (pvar x)))*(free_occ_t z t) 
        else (free_occ_t y (val_to_term (pvar x)))*(free_occ_t z t)
                 +(free_occ_t z (val_to_term (pvar x))) ))
 (match veqb y x
 return λb. veqb y x = b → 1 ≤ 1 →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb y x = true.
        λp: 1 ≤ 1.
         «t, gg H p»
     | false ⇒ λH: veqb y x = false.
        λp: 1 ≤ 1.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb y x )) (le_n 1)))  (val_to_term (pvar x)))
[2: #UU @(UU …)] #gg #tt >H in gg tt ⊢ %; #gg' #tt' normalize // qed.

lemma no_subst2: ∀x, t, u. pif_subst (val_to_term (abstr x t)) (psubst x u) = (val_to_term (abstr x t)).
#x #t1 #t'
change with (pi1 … (pif_subst_sig …)) in match (pif_subst (val_to_term (abstr x t1)) (psubst x t'));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match ((t_size (val_to_term (abstr x t1))));

normalize in match ((pif_subst_sig (S (t_size t1)) x t' (val_to_term (abstr x t1))));

cut (∀K, K1, K2, K3. pi1 pifTerm (λu:pifTerm
   .t_size u=S (plus (t_size t1) (times (free_occ_t x (val_to_term (abstr x t1))) (minus (t_size t') 1)))
    ∧(∀z:Variable
      .free_occ_t z u
       =if veqb x z 
        then (free_occ_t z (val_to_term (abstr x t1)))*(free_occ_t z t') 
        else (free_occ_t x (val_to_term (abstr x t1)))*(free_occ_t z t')
                 +free_occ_t z (val_to_term (abstr x t1)) ))
 (match veqb x x return λb. veqb x x = b → t_size (val_to_term (abstr x t1)) ≤ S (t_size t1) → Σu: pifTerm. ?
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr x t1)), K H p»
        | false ⇒ λH. match fvb_t x t' return λb. fvb_t x t'=b → t_size (val_to_term (abstr x t1)) ≤ S (t_size t1) → Σu: pifTerm. ?
         with
          [ true ⇒ λHH. match fvb_t x (val_to_term (abstr x t1)) return λHfvb. fvb_t x (val_to_term (abstr x t1)) = Hfvb →  t_size (val_to_term (abstr x t1)) ≤ S (t_size t1) → Σu: pifTerm. ? 
            with
            [ true ⇒ λHfv.λp. let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig (t_size t1) x (val_to_term (pvar ν(z))) t1 (le_n (t_size t1))) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size t1) x t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr x t1)), K2 H HH Hfv p»
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr x (pi1 … (pif_subst_sig (t_size t1) x t' t1 (le_n (t_size t1)))))), K3 H HH p»
          ] (refl …)
        ]  (refl bool (veqb x x)) (le_n (S (t_size t1))))= val_to_term (abstr x t1));
   [ 2: #K @K | #K #K1 #K2 #K3 >veqb_true in K K1 K2 K3 ⊢ %; normalize #K #K1 #K2 #K3 //]
qed.
(*
lemma abstr_step_subst: ∀x, y, t, u.
 veqb y x =false →
  pif_subst (val_to_term (abstr x t)) (psubst y u) = (val_to_term (abstr x (pif_subst t (psubst y u)))).

#x #y #t #u #H
change with (pi1 … (pif_subst_sig …)) in match (pif_subst (val_to_term (abstr x t)) (psubst y u));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);

cut (∀K, K1, K2. pi1 pifTerm
  (λu0:pifTerm
   .t_size u0
    =t_size (val_to_term (abstr x t))
     +free_occ_t y (val_to_term (abstr x t))*(t_size u-1)
    ∧(∀z:Variable
      .free_occ_t z u0
       =if veqb y z 
        then free_occ_t z (val_to_term (abstr x t))*free_occ_t z u 
        else free_occ_t y (val_to_term (abstr x t))*free_occ_t z u
                 +free_occ_t z (val_to_term (abstr x t)) ))
 (match veqb y x return λb. veqb y x = b → S (t_size t) ≤ S (t_size t) →
    Σu: pifTerm. ?
 with
  [ true ⇒ λH: veqb y x =true.
     λp: S (t_size t ) ≤ S (t_size t).
       «val_to_term (abstr x t), K H p »
  |  false  ⇒ λH: veqb y x =false. match fvb_t x u return λb'. fvb_t x u = b' →
                                       S (t_size t) ≤ S (t_size t) →
                                        Σu: pifTerm. ?
              with
              [ true ⇒ λHH: fvb_t x u = true. λp:S (t_size t) ≤ S (t_size t). let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t) (fresh_var_t u))))
                  in match (pif_subst_sig (t_size t) (psubst x (val_to_term (pvar ν(z)))) t (le_n ?)) with
                     [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size t) (psubst y u) a (subst_aux_5 … h p))))), K1 H HH p a h»]
              | false ⇒ λHH: fvb_t x u = false. λp:S (t_size t) ≤ S (t_size t). «(val_to_term (abstr x (pi1 … (pif_subst_sig (t_size t) (psubst y u) t (le_n ?))))), K2 H HH p »
              ] (refl bool (fvb_t x u))

  ] (refl bool (veqb y x))  (le_n (S (t_size t))))= val_to_term (abstr x (pif_subst t (psubst y u))))
  [ 2: #UU   >UU
  *)

axiom pif_subst_bound_irrelevance:
 ∀n, n', t, y, t'. t_size t ≤ n →
  t_size t ≤ n' →
   pif_subst_sig n y t' t ? = pif_subst_sig n' y t' t ?.//qed.

lemma pif_subst_distro0:
 ∀n1, n2, t1, t2, y, t'.
  t_size t1 = n1 →
   t_size t2 = n2  →
   pi1 … (pif_subst_sig (S (n1 + n2)) y t' (appl t1 t2) ?) = appl (pi1 … (pif_subst_sig n1 y t' t1 ?)) (pi1 … (pif_subst_sig n2 y t' t2 ?)).

[  #n1 #n2 #t1 #t2 #y #t' #H1 #H2 whd in ⊢ (? ? % ?);  @eq_f2
  @eq_f @pif_subst_bound_irrelevance
| normalize //
| //
| //
]
qed.

lemma pif_subst_distro:
 ∀t1, t2, s. pif_subst (appl t1 t2) s = appl (pif_subst t1 s) (pif_subst t2 s).

#t1 #t2 * #y #t'
change with (pi1 … (pif_subst_sig (t_size (appl t1 t2)) y t' (appl t1 t2) ?)) in match (pif_subst (appl t1 t2) (psubst y t'));
change with (pi1 … (pif_subst_sig (t_size t1) y t' t1 ?)) in match (pif_subst t1 (psubst y t'));
change with (pi1 … (pif_subst_sig (t_size t2) y t' t2 ?)) in match (pif_subst t2 (psubst y t'));
change with (S ((t_size t1) + (t_size t2))) in match (t_size (appl t1 t2));
@pif_subst_distro0 // qed.


lemma no_subst4:
 (∀t.∀y. ∀t'. fvb_t (νy) t =false → pif_subst t (psubst (νy) t')=t) ∧
  (∀v.∀y. ∀t'. fvb_tv (νy) v =false → pif_subst (val_to_term v) (psubst (νy) t')=(val_to_term v)).
@pifValueTerm_ind

[ #v #H #y normalize @H
| #t1 #t2 #H1 #H2 #y #t' >pif_subst_distro #H
  cut (fvb_t (νy) t1 =false ∧ fvb_t (νy) t2 =false)
  [ lapply H normalize #Hgtb lapply (gtb_O … Hgtb) #Hplus
    cut (free_occ_t (νy) t1=0 ∧ free_occ_t (νy) t2=0)
    [ % /2/] * #Ht1 #Ht2 >Ht1 >Ht2 normalize /2/
  ] * #Ht1 #Ht2  >(H1 … Ht1) >(H2 … Ht2) //
| * #x #y #t' #H normalize in H; @no_subst normalize lapply H
  cases neqb normalize [ #abs destruct | // ]
| #t1 * #x #HI #y #t' #H
  cut (neqb y x = true ∨ neqb y x = false) // * #Htf
  [ lapply (neqb_iff_eq y x) * #Heq #_ lapply (Heq Htf)
    -Heq #Heq destruct @no_subst2
  | normalize in H; >Htf in H; >if_f #H
    cut (veqb (νy) (νx) = false ∧ (fvb_t (νy) (val_to_term (abstr (νx) t1))=false))
    [ % // normalize >Htf normalize @H
    | * #Hneqb #Hinb
    change with (pi1 pifTerm ? ?) in match (pif_subst ? ?);
    whd in match (match ? in pifSubst with [_⇒ ?]);
    whd in match (match ? in pifSubst with [_⇒ ?]);
    cut (∀K, K1, K2, K3. pi1 pifTerm (λu:pifTerm
   .t_size u
    =t_size (val_to_term (abstr (νx) t1))
     +free_occ_t (νy) (val_to_term (abstr (νx) t1))*(t_size t'-1)
    ∧(∀z:Variable
      .free_occ_t z u
       =if veqb (νy) z 
        then free_occ_t z (val_to_term (abstr (νx) t1))*free_occ_t z t' 
        else free_occ_t (νy) (val_to_term (abstr (νx) t1))*free_occ_t z t'
                 +free_occ_t z (val_to_term (abstr (νx) t1)) ))
 (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S (t_size t1) → Σu: pifTerm. ?
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), K H p»
        | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S (t_size t1) → Σu: pifTerm. ?
         with
          [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S (t_size t1) → Σu: pifTerm. ? 
            with
            [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig (t_size t1) (νx) (val_to_term (pvar ν(z))) t1 (le_n (t_size t1))) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size t1) (νy) t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), K2 H HH Hfv p»
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig (t_size t1) (νy) t' t1 (le_n (t_size t1)))))), K3 H HH p»
          ] (refl …)
        ]  (refl bool (veqb (νy) (νx))) (le_n (S (t_size t1))))= val_to_term (abstr (νx) t1))
    [2: #UU @UU ] #K #K1 #K2 #K3 >Hneqb in K K1 K2 K3 ⊢%; #K #K1 #K2 #K3 
    cases (fvb_t (νx) t') in K K1 K2 K3 ⊢ %; #K #K1 #K2 #K3
    [ >Hinb in K K1 K2 K3 ⊢ %; #K #K1 #K2 #K3 /2/
    | >Hinb in K K1 K2 K3 ⊢ %; #K #K1 #K2 #K3
      cut (fvb_t (νy) t1 =false)
      [ lapply H lapply Hneqb normalize #Hyhy >Hyhy //
      | #Hyee lapply (HI … t' Hyee) -HI #HI normalize @eq_f @eq_f normalize in HI; >HI //
      ]
    ]
  ]
] qed.

lemma no_subst3:
 (∀t.∀y. ∀t'. inb_t (νy) t =false → pif_subst t (psubst (νy) t')=t) ∧
  (∀v.∀y. ∀t'. inb_tv (νy) v =false → pif_subst (val_to_term v) (psubst (νy) t')=(val_to_term v)).

lapply fv_to_in_term * #Hin1 #Hin2
lapply no_subst4 * #Hno1 #Hno2 % 
[ #t #y #t' #H cut (fvb_t (νy) t=false)
  [ lapply (Hin1 t (νy)) -Hin1 #Hin1
    cut (inb_t (νy) t=false→ fvb_t (νy) t=false)
    [ lapply Hin1 cases fvb_t cases inb_t // #H #_ >H //
    | -Hin1 #Hin1 @Hin1 @H
    ]
  | #Hfv @Hno1 @Hfv
  ]
| #v #y #t' #H cut (fvb_tv (νy) v=false)
  [ lapply (Hin2 v (νy)) -Hin2 #Hin2
    cut (inb_tv (νy) v=false→ fvb_tv (νy) v=false)
    [ lapply Hin2 cases fvb_tv cases inb_tv // #H #_ >H //
    | -Hin2 #Hin2 @Hin2 @H
    ]
  | #Hfv @Hno2 @Hfv
  ]
] qed.

lemma fresh_var_pif_subst:
 (∀t, y, t'. inb_t y t=false → fresh_var_t (pif_subst t (psubst y t')) ≤ max (fresh_var_t t) (fresh_var_t t')) ∧
  (∀v, y, t'. inb_tv y v=false → fresh_var_t (pif_subst (val_to_term v) (psubst y t')) ≤ max (fresh_var_tv v) (fresh_var_t t')).

@pifValueTerm_ind
[ normalize #v #H @H
| #t1 #t2 #H1 #H2 #y #t' >pif_subst_distro
  whd in match (fresh_var_t (appl ? ?));
  whd in match (fresh_var_t (appl t1 t2));
  change with (fresh_var_t (pif_subst t1 ?))
    in match (pi1 ? ? (fresh_var_t_Sig (pif_subst ? ?)));
  change with (fresh_var_t (pif_subst t2 ?))
    in match (pi1 ? ? (fresh_var_t_Sig (pif_subst t2 ?)));
  change with (fresh_var_t t1 )
    in match (pi1 ? ? (fresh_var_t_Sig t1 ));
  change with (fresh_var_t t2)
    in match (pi1 ? ? (fresh_var_t_Sig t2));
  change with (orb ? ?) in match (if ? then ? else ?);
  #Hin
  cut (inb_t y t1=false ∧ inb_t y t2=false)
  [ % lapply Hin cases inb_t cases inb_t //
    whd in match (true ∨ true); //
  ]
  * -Hin #Hin1 #Hin2 
  change with (max ? ?) in match (if ? then ? else ?);
  change with (max ? ?) in match (if ? then ? else (fresh_var_t t1));
  cut ((max (fresh_var_t (pif_subst t1 (psubst y t')))
            (fresh_var_t (pif_subst t2 (psubst y t'))) ≤
        max (max (fresh_var_t t1) (fresh_var_t t'))
            (max (fresh_var_t t2) (fresh_var_t t'))))
  [ @to_max
    [ cut (max (fresh_var_t t1) (fresh_var_t t') ≤ 
           max (max (fresh_var_t t1) (fresh_var_t t'))
                (max (fresh_var_t t2) (fresh_var_t t')))
      [ @le_n_max_n
      | #Hm @(transitive_le … (H1 … Hin1) Hm)
      ]
    | cut (max (fresh_var_t t2) (fresh_var_t t') ≤ 
           max (max (fresh_var_t t1) (fresh_var_t t'))
                (max (fresh_var_t t2) (fresh_var_t t')))
      [ >(max_comm (max ? ?) ?) @le_n_max_n
      | #Hm @(transitive_le … (H2 … Hin2) Hm)
      ]
    ]
  | #H //
  ]
| #x #y #t #Hin cut (veqb x y = false)
  [ lapply Hin normalize //]
    #Hveqb >no_subst [ @le_n_max_n | >veqb_comm assumption ]
| #t1 * #x #HI * #y #t' #H cut (veqb (νy) (νx) = false ∧ (fvb_t (νy) (val_to_term (abstr (νx) t1))=false))
    [ % lapply H normalize cases neqb // normalize #H destruct 
      change with (fvb_t ? ?) in match (gtb ? ?);
      lapply (fv_to_in_term) * #Hintofv #_
      cut (inb_t (νy) t1 = false → fvb_t (νy) t1 = false)
      [ lapply (Hintofv t1 (νy)) cases fvb_t cases inb_t // #Ht #_ >Ht //]
      #Hf >Hf //
    | * #Hveqb #Hfvb
      change with (max ? (fresh_var_t ?)) in match (fresh_var_tv ?);
      change with (pi1 pifTerm ? ?) in match (pif_subst ? ?);
      whd in match (match ? in pifSubst with [_⇒ ?]);
      whd in match (match ? in pifSubst with [_⇒ ?]);
      cut (∀K, K1, K2, K3. fresh_var_t (pi1 pifTerm (λu:pifTerm
     .t_size u
      =t_size (val_to_term (abstr (νx) t1))
       +free_occ_t (νy) (val_to_term (abstr (νx) t1))*(t_size t'-1)
      ∧(∀z:Variable
        .free_occ_t z u
         =if veqb (νy) z 
          then free_occ_t z (val_to_term (abstr (νx) t1))*free_occ_t z t' 
          else free_occ_t (νy) (val_to_term (abstr (νx) t1))*free_occ_t z t'
                   +free_occ_t z (val_to_term (abstr (νx) t1)) ))
      (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S (t_size t1) → Σu: pifTerm. ?
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), K H p»
        | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S (t_size t1) → Σu: pifTerm. ?
         with
          [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S (t_size t1) → Σu: pifTerm. ? 
            with
            [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig (t_size t1) (νx) (val_to_term (pvar ν(z))) t1 (le_n (t_size t1))) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (t_size t1) (νy) t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), K2 H HH Hfv p»
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig (t_size t1) (νy) t' t1 (le_n (t_size t1)))))), K3 H HH p»
          ] (refl …)
        ]  (refl bool (veqb (νy) (νx))) (le_n (S (t_size t1)))))≤ max (max (S x) (fresh_var_t t1)) (fresh_var_t t'))
    [2: #UU @UU]  lapply Hveqb >veqb_comm -Hveqb #Hveqb #K #K1 #K2 #K3
    >Hveqb in K K1 K2 K3 ⊢%; #K #K1 #K2 #K3
    cut (fvb_t (νx) t' = true ∨ fvb_t (νx) t' = false) // * #Hfvbxt'
    >Hfvbxt' in K K1 K2 K3; #K #K1 #K2 #K3
    [ >Hfvb in K K1 K2 K3; #K #K1 #K2 #K3
      normalize
      change with (max (S x) ?) in match (if ? then ? else S x);
      change with (max ? ?) in match (if ? then ? else (max ? ?));
      change with (fresh_var_t t1 )
        in match (pi1 ? ? (fresh_var_t_Sig t1 ));
      @le_n_max_n
    | normalize
      change with (max (S x) ?) in match (if ? then ? else S x);
      change with (pif_subst ? (psubst (νy) t')) in match ((pi1 pifTerm
      (λu:pifTerm
      .t_size u=t_size t1+free_occ_t (νy) t1*(t_size t'-1)
       ∧(∀z:Variable
         .free_occ_t z u
          =if match z in Variable return λ_:Variable.bool with 
                [variable (m1:ℕ)⇒neqb y m1] 
           then free_occ_t z t1*free_occ_t z t' 
           else free_occ_t (νy) t1*free_occ_t z t'+free_occ_t z t1 ))
      (pif_subst_sig (t_size t1) (νy) t' t1 (le_n (t_size t1)))));
      change with (fresh_var_t ?) in match (pi1 ? ?
        (fresh_var_t_Sig (pif_subst t1 (psubst (νy) t'))));
      change with (fresh_var_t t1)
        in match (pi1 ? ? (fresh_var_t_Sig t1 ));
      change with (fresh_var_t t')
        in match (pi1 ? ? (fresh_var_t_Sig t'));
      change with (leb (S x) ?)
        in match (match fresh_var_t t1 in nat with [_⇒ ?]);
      change with (max ? (fresh_var_t t'))
        in match (if leb ? (fresh_var_t t') then ? else ?);
      change with (max ? ?)
        in match (if leb (S x) (fresh_var_t t1) then fresh_var_t t1 else S x );
      @to_max
      [ @(le_maxl … (fresh_var_t t1)) @le_n_max_n
      | cut (fresh_var_t (pif_subst t1 (psubst (νy) t')) ≤
             max (fresh_var_t t1) (fresh_var_t t'))
        [ @HI lapply H normalize cases neqb normalize #H destruct //
        | #Hm cut (max (fresh_var_t t1) (fresh_var_t t') ≤
                   max (max (S x) (fresh_var_t t1)) (fresh_var_t t'))
          [ //
          | #Hm2 @(transitive_le … Hm Hm2)
          ]
        ]
      ]
    ]
  ]
] qed.

