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

lemma pif_subst_bound_irrelevance0: ∀n.
 (∀t, n', y, t', H, H'.
   pif_subst_sig n y t' t H = pif_subst_sig n' y t' t H').

@nat_ind
[ *
  [ *
    [ #x #n' #y #t' #H @False_ind lapply H normalize /2/
    | #x #t #n' #y #t' #H @False_ind lapply H normalize /2/
    ]
  | #t1 #t2 #n' #y #t' #H @False_ind lapply H normalize /2/
  ]
]
#m #HI *
[ *
  [ #x #n' cases n'
    [ #y #t' #H #H' @False_ind lapply H' /2/ ] #m'
    #y #t' #H #H'
    whd in match (pif_subst_sig ? ? ? ? ?);
    whd in match (pif_subst_sig ? ? ? ? ?);
    whd in match (match psubst y t' in pifSubst with [psubst y t'⇒t']);
    cut (∀AAA,BBB,CCC,DDD.
     ((match veqb y x return λb. veqb y x = b → t_size (val_to_term (pvar x))≤S m → Σu:pifTerm. ?
       with
       [ true ⇒ (λH0:veqb y x=true
               .λp:t_size (val_to_term (pvar x))≤S m.«t',AAA H0 p») 
       | false ⇒ (λH0:veqb y x=false
               .λp:t_size (val_to_term (pvar x))≤S m
                .«val_to_term (pvar x), BBB … H0 p ») 
       ])
    (refl bool (veqb y x)) H)
    =((match veqb y x return λb. veqb y x = b → t_size (val_to_term (pvar x))≤S m' → Σu:pifTerm. ?
       with
       [ true ⇒ (λH0:veqb y x=true
                .λp:t_size (val_to_term (pvar x))≤S m'.«t',CCC H0 p») 
       | false ⇒ (λH0:veqb y x=false
                .λp:t_size (val_to_term (pvar x))≤S m'
                 .«val_to_term (pvar x),DDD … H0 p »)
       ])) (refl bool (veqb y x)) H')
    [ 3: #uu @uu | skip ]
    cut (veqb y x = true ∨ veqb y x = false) // * #Hyx >Hyx
    normalize >Hyx normalize //
    | * #x #t1 #n'
      cases n'
      [ #y #t' #H #H' @False_ind lapply H' /2/ ] #m'
      * #y #t' #H #H'
      whd in match (pif_subst_sig ? ? ? ? ?);
      whd in match (pif_subst_sig (S m') (νy) t' (val_to_term (abstr (νx) t1)) H');
      whd in match (match ? in Variable with [_ ⇒?]);
      whd in match (match ? in Variable with [_ ⇒?]);
      cut (∀AAA,BBB,CCC,DDD,EEE,FFF,GGG,HHH.
         (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S m → Σu: pifTerm. ?
           with
            [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), AAA H p»
            | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S (m) → Σu: pifTerm. ?
             with
              [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S (m) → Σu: pifTerm. ?
                with
                [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                       in match (pif_subst_sig (m) (νx) (val_to_term (pvar ν(z))) t1 (subst_aux_7 (νx) t1 m p)) with
                   [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (m) (νy) t' a (subst_aux_5 … h p))))), BBB H HH Hfv p a h »]
                | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), CCC H HH Hfv p»
                ] (refl …)
              | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig (m) (νy) t' t1 (subst_aux_7 (νx) t1 m p))))), DDD H HH p»
              ] (refl …)
            ]  (refl bool (veqb (νy) (νx))) H)

            =

          (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S m' → Σu: pifTerm. ?
           with
            [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), EEE H p»
            | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S (m') → Σu: pifTerm. ?
             with
              [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S (m') → Σu: pifTerm. ?
                with
                [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                       in match (pif_subst_sig (m') (νx) (val_to_term (pvar ν(z))) t1 (subst_aux_7 (νx) t1 m' p)) with
                   [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (m') (νy) t' a (subst_aux_5 … h p))))), FFF H HH Hfv p a h »]
                | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), GGG H HH Hfv p»
                ] (refl …)
              | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig (m') (νy) t' t1 (subst_aux_7 (νx) t1 m' p))))), HHH H HH p»
              ] (refl …)
            ]  (refl bool (veqb (νy) (νx))) H')
            )
      [ 3: #UUU @UUU | skip ]
      cases (veqb (νy)(νx))
      [ #AAA #BBB #CCC #DDD #EEE #FFF #GGG #HHH normalize //
      | cases (fvb_t (νx) t')
        [ 2: #AAA #BBB #CCC #DDD #EEE #FFF #GGG #HHH normalize
          >(HI t1 m' (νy) t') in AAA BBB CCC DDD EEE FFF GGG HHH ⊢%; /2/ ]
          cut (fvb_t (νy) (val_to_term (abstr (νx) t1))=true ∨ fvb_t (νy) (val_to_term (abstr (νx) t1))=false) // *
          #Hfvyt1 >Hfvyt1
          [ 2: #AAA #BBB #CCC #DDD #EEE #FFF #GGG #HHH normalize // ]
          #AAA #BBB #CCC #DDD #EEE #FFF #GGG #HHH
          >(HI t1 m' (νx)
          (val_to_term (pvar ν(max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t')))))) )
          in AAA BBB CCC DDD EEE FFF GGG HHH ⊢%;
          [ 2: lapply H' normalize /2/
          | 3: lapply H normalize /2/
          ]
        cases (pif_subst_sig m' (νx) …) #a #h
        #AAA #BBB #CCC #DDD #EEE #FFF #GGG #HHH
        change with
        (( « (val_to_term (abstr (ν(?)) (pi1 … (pif_subst_sig (m) (νy) t' a (subst_aux_5 … h ?))))), BBB (refl …) (refl …) (refl …) H a h »)
            =
          « (val_to_term (abstr (ν(?)) (pi1 … (pif_subst_sig (m') (νy) t' a (subst_aux_5 … h ?))))), FFF (refl …) (refl …) (refl …) H' a h »
        )
        cut (∀KKK,JJJ,LLL,MMM.
         («val_to_term
       (abstr (ν(max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t')))))
        (pi1 pifTerm
         (λu:pifTerm
          .t_size u=t_size a+free_occ_t (νy) a*(t_size t'-1)
           ∧(∀z:Variable
             .free_occ_t z u
              =if veqb (νy) z 
               then free_occ_t z a*free_occ_t z t' 
               else free_occ_t (νy) a*free_occ_t z t'+free_occ_t z a ))
         (pif_subst_sig m (νy) t' a KKK))),
      LLL … »
      =«val_to_term
        (abstr (ν(max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t')))))
         (pi1 pifTerm
          (λu:pifTerm
           .t_size u=t_size a+free_occ_t (νy) a*(t_size t'-1)
            ∧(∀z:Variable
              .free_occ_t z u
               =if veqb (νy) z 
                then free_occ_t z a*free_occ_t z t' 
                else free_occ_t (νy) a*free_occ_t z t'+free_occ_t z a ))
          (pif_subst_sig m' (νy) t' a JJJ))),
       MMM … »))
       [3: #UUU @UUU | skip ] #KKK #JJJ #LLL #MMM
        >(HI a m' (νy) t' KKK JJJ) in AAA BBB CCC DDD EEE FFF GGG HHH LLL MMM ; /2/
       ]
     ]
  | #t1 #t2 #n' cases n'
    [ #y #H #H1 #H2 @False_ind lapply H2 /2/ ] #m'
    #y #t' #H1 #H2
    change with (mk_Sig … (appl (pi1 …(pif_subst_sig m y t' t1 ? )) (pi1 … (pif_subst_sig m y t' t2 ?))) ?)
      in match (pif_subst_sig (S m) y t' (appl t1 t2) H1);
    change with (mk_Sig … (appl (pi1 …(pif_subst_sig m' y t' t1 ? )) (pi1 … (pif_subst_sig m' y t' t2 ?))) ?)
      in match (pif_subst_sig (S m') y t' (appl t1 t2) H2);
      >(HI t1 m' y t' ? (subst_aux_10 t1 t2 m' H2))
      >(HI t2 m' y t' … (subst_aux_9 t1 t2 m' H2)) //
] qed.

lemma pif_subst_bound_irrelevance:
 ∀n, n', t, y, t', H, H'.
   pif_subst_sig n y t' t H = pif_subst_sig n' y t' t H'.
#n #n' #y #y #t' #H #H' @pif_subst_bound_irrelevance0 qed.

lemma pif_subst_distro0:
 ∀n1, n2, t1, t2, y, t', H, H1, H2.
   pi1 … (pif_subst_sig (S (n1 + n2)) y t' (appl t1 t2) H) = appl (pi1 … (pif_subst_sig n1 y t' t1 H1)) (pi1 … (pif_subst_sig n2 y t' t2 H2)).

#n1 #n2 #t1 #t2 #y #t' #H #H1 #H2
whd in match (pif_subst_sig (S (n1+n2)) y t' (appl t1 t2) H); @eq_f2  @eq_f
 @pif_subst_bound_irrelevance qed.

lemma atomic_subst0: ∀n,y,t',H. pi1 pifTerm ? (pif_subst_sig n y t' (val_to_term (pvar y)) H) = t'.
@nat_ind
[ #x #t #H @False_ind lapply H /2/ ]
#n #_ #x #t #H
whd in match (pif_subst_sig (S n) x t ? H);
cut (∀gg.∀ tt. (pi1 pifTerm ?
 (match veqb x x
 return λb. veqb x x = b → 1 ≤ S n →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb x x = true.
        λp: 1 ≤ S n.
         «t, gg H p»
     | false ⇒ λH: veqb x x = false.
        λp: 1 ≤ S n.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb x x )) (H))) = t)
     [ 3: #gg >(gg …) /3/ | 1: skip]
  #gg #tt >(veqb_true …) in gg tt ⊢ %;
  normalize // qed.

lemma no_subst0: ∀n,x,y,t',H. veqb x y = false → pi1 pifTerm ? (pif_subst_sig n x t' (val_to_term (pvar y)) H) = (val_to_term (pvar y)).
@nat_ind
[ #x #y #t' #H @False_ind lapply H /2/ ]
#n #HI #y #x #t #H1 #H
whd in match (pif_subst_sig (S n) y t (val_to_term (pvar x)) (?));
cut (∀gg.∀ tt. eq pifTerm (pi1 pifTerm ?
 (match veqb y x
 return λb. veqb y x = b → 1 ≤ S n →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb y x = true.
        λp: 1 ≤ S n.
         «t, gg H p»
     | false ⇒ λH: veqb y x = false.
        λp: 1 ≤ S n.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb y x )) (H1)))  (val_to_term (pvar x)))
[3: #UU @(UU …) | skip ] #gg #tt >H in gg tt ⊢ %; #gg' #tt' normalize // qed.

lemma no_subst20: ∀n,x,t1,t',H.
 pi1 pifTerm ? (pif_subst_sig n x t' (val_to_term (abstr x t1)) H) = (val_to_term (abstr x t1)).

*
[ #x #t1 #t' #H @False_ind lapply H normalize /2/]
#n #x #t1 #t' #H

whd in match (pif_subst_sig (S n) x t' (val_to_term (abstr x t1)) H);

cut (∀K, K1, K2, K3. pi1 pifTerm ?
 (match veqb x x return λb. veqb x x = b → t_size (val_to_term (abstr x t1)) ≤ S n → Σu: pifTerm. ?
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr x t1)), K H p»
        | false ⇒ λH. match fvb_t x t' return λb. fvb_t x t'=b → t_size (val_to_term (abstr x t1)) ≤ S n → Σu: pifTerm. ?
         with
          [ true ⇒ λHH. match fvb_t x (val_to_term (abstr x t1)) return λHfvb. fvb_t x (val_to_term (abstr x t1)) = Hfvb →  t_size (val_to_term (abstr x t1)) ≤ S n → Σu: pifTerm. ?
            with
            [ true ⇒ λHfv.λp. let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig n x (val_to_term (pvar ν(z))) t1 ?) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig n x t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr x t1)), K2 H HH Hfv p»
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr x (pi1 … (pif_subst_sig n x t' t1 ?)))), K3 H HH p»
          ] (refl …)
        ]  (refl bool (veqb x x)) H)= val_to_term (abstr x t1))
   [ 5: #K @K | 1,2,3: skip ] >veqb_true //
qed.

lemma abstr_step_subst0: ∀n, x, y, t1, t', H1, H2.
 veqb y x =false →
  fvb_t x t' = false →
   (pi1 pifTerm ? (pif_subst_sig n y t' (val_to_term (abstr x t1)) H1)) =
   (val_to_term (abstr x (pi1 pifTerm ? (pif_subst_sig n y t' t1 H2)))).
@nat_ind
[ #x #y #t1 #t' #H1 @False_ind lapply H1 normalize /2/ ]
#n #HI * #x * #y #t1 #t' #H1 #H2 #Hveq #Hfv
cut (∀K, K1, K2, K3. pi1 pifTerm ?
 (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S (n) → Σu: pifTerm. ?
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), K H p»
        | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S (n) → Σu: pifTerm. ?
         with
          [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S (n) → Σu: pifTerm. ?
            with
            [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                   in match (pif_subst_sig (n) (νx) (val_to_term (pvar ν(z))) t1 ?) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig ? (νy) t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), K2 H HH Hfv p»
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig n (νy) t' t1 ?)))), K3 H HH p»
          ] (refl …)
        ]  (refl bool (veqb (νy) (νx))) H1)
        = val_to_term (abstr (νx) (pi1 pifTerm ? (pif_subst_sig (S n) (νy) t' t1 H2))))
 [ 5: #UU @UU | 1,2,3: skip] >Hveq  >Hfv #K #K1 #K2 #K3
 change with
 (val_to_term (abstr (νx) (pi1 pifTerm ? (pif_subst_sig n (νy) t' t1 (subst_aux_7 (νx) t1 n H1))))
 =
 val_to_term (abstr (νx) (pi1 pifTerm ? (pif_subst_sig (S n) (νy) t' t1 H2))))
  @eq_f @eq_f @eq_f // qed.

lemma no_subst50:
 (∀n,t.∀y.∀t',H. fvb_t (y) t =false → pi1 pifTerm ? (pif_subst_sig n y t' t H)=t).
@nat_ind
[ *
  [ *
    [ #x #y #t' #H @False_ind lapply H /2/
    | #x #t1 #y #t' #H @False_ind lapply H /2/
    ]
  | #t1 #t2 #y #t' #H @False_ind lapply H /2/
  ]
]
#n #HI *
[ *
  [ #z #y #t' #H1 #H2 @no_subst0
    lapply H2 normalize cases veqb // normalize #H @H
  | * #x #t1 * #y #t' #H1 #H2
    cut (neqb y x = true ∨ neqb y x = false) // * #Htf
    [ elim (neqb_iff_eq y x) #Heq #_ lapply (Heq Htf) -Heq #Heq destruct
      @no_subst20
    | normalize in H2; >Htf in H2; >if_f #H2
      cut (veqb (νy) (νx) = false ∧ (fvb_t (νy) (val_to_term (abstr (νx) t1))=false))
      [ % // normalize >Htf normalize @H2 ]
      * #Hneqb #Hinb

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
   (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S n → Σu: pifTerm. ?
         with
          [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), K H p»
          | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S (n) → Σu: pifTerm. ?
           with
            [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S (n) → Σu: pifTerm. ?
              with
              [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                     in match (pif_subst_sig (n) (νx) (val_to_term (pvar ν(z))) t1 (subst_aux_7 (νx) t1 n p)) with
                 [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig (n) (νy) t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
              | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), K2 H HH Hfv p»
              ] (refl …)
            | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig (n) (νy) t' t1 (subst_aux_7 (νx) t1 n p))))), K3 H HH p»
            ] (refl …)
          ]  (refl bool (veqb (νy) (νx))) H1)= val_to_term (abstr (νx) t1))
    [ 2: #UU @UU ] >Hneqb 
    cases (fvb_t (νx) t')
      [ >Hinb /2/
      | >Hinb
        cut (fvb_t (νy) t1 =false)
        [ lapply H1 lapply Hneqb normalize #Hyhy >Hyhy //
        | #Hyee lapply (HI t1 (νy) t' (subst_aux_7 (νx) t1 n H1) Hyee) -HI #HI
          #K #K1 #K2 #K3 normalize @eq_f @eq_f normalize in HI; @HI
        ]
      ]
    ]
  ]
| #t1 #t2 #y #t' #H1 #H2
  >(pif_subst_bound_irrelevance ? (S ((t_size t1)+(t_size t2))) (appl t1 t2) y t')
  [ 2: normalize //] >pif_subst_distro0
  [ 2,3: //]
  @eq_f2
  [
    >(pif_subst_bound_irrelevance ? n t1 y t' ? (subst_aux_10 t1 t2 n H1))
    @(HI t1) lapply H2 normalize cases free_occ_t normalize //
  | >(pif_subst_bound_irrelevance ? n t2 y t' ? (subst_aux_9 t1 t2 n H1))
    @(HI t2) lapply H2 normalize cases free_occ_t normalize // #n #abs destruct
] qed.

lemma no_subst30:
 (∀n,t, y,t', H. inb_t y t =false → 
   (pi1 pifTerm ? (pif_subst_sig n y t' t H))=t).
 
lapply fv_to_in_term * #Hin1 #_
#n #t #y #t'#H #H1 @no_subst50
@(bool_impl_inv2 Variable pifTerm Variable pifTerm inb_t fvb_t y y t t false false) // @Hin1
qed.

lemma fresh_var_pif_subst0:
 (∀n, t, y, t', H. inb_t y t=false →
  fresh_var_t (pi1 pifTerm ? (pif_subst_sig n y t' t H)) ≤ max (fresh_var_t t) (fresh_var_t t')).

@nat_ind
[ *
  [ *
    [ #x #y #t' #H @False_ind lapply H /2/
    | #x #t1 #y #t' #H @False_ind lapply H /2/
    ]
  | #t1 #t2 #y #t' #H @False_ind lapply H /2/
  ]
]
#n #HI
*
[ *
  [ #x #y #t #H #Hin >no_subst30 //
  | * #x #t1 * #y #t' #H1 #H cut (veqb (νy) (νx) = false ∧ (fvb_t (νy) (val_to_term (abstr (νx) t1))=false))
    [ % lapply H normalize cases neqb // normalize #H destruct
      change with (fvb_t ? ?) in match (gtb ? ?);
      lapply (fv_to_in_term) * #Hintofv #_
      @(bool_impl_inv2 Variable pifTerm Variable pifTerm inb_t fvb_t (νy) (νy) t1 t1 false false) //
      @Hintofv 
      | * #Hveqb #Hfvb
        change with (max ? (fresh_var_t ?)) in match (fresh_var_tv ?);
        cut (∀K, K1, K2, K3. fresh_var_t (pi1 pifTerm ?
        (match veqb (νy) (νx) return λb. veqb (νy) (νx) = b → t_size (val_to_term (abstr (νx) t1)) ≤ S n → Σu: pifTerm. ?
         with
          [ true ⇒ λH.λp. « (val_to_term (abstr (νx) t1)), K H p»
          | false ⇒ λH. match fvb_t (νx) t' return λb. fvb_t (νx) t'=b → t_size (val_to_term (abstr (νx) t1)) ≤ S n → Σu: pifTerm. ?
           with
            [ true ⇒ λHH. match fvb_t (νy) (val_to_term (abstr (νx) t1)) return λHfvb. fvb_t (νy) (val_to_term (abstr (νx) t1)) = Hfvb →  t_size (val_to_term (abstr (νx) t1)) ≤ S n → Σu: pifTerm. ?
              with
              [ true ⇒ λHfv.λp. let z ≝ (max (S y) (max (S x) (max (fresh_var_t t1) (fresh_var_t t'))))
                     in match (pif_subst_sig n (νx) (val_to_term (pvar ν(z))) t1 ?) with
                 [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig n (νy) t' a (subst_aux_5 … h p))))), K1 H HH Hfv p a h »]
              | false ⇒ λHfv. λp. « (val_to_term (abstr (νx) t1)), K2 H HH Hfv p»
              ] (refl …)
            | false ⇒ λHH. λp. « (val_to_term (abstr (νx) (pi1 … (pif_subst_sig n (νy) t' t1 ?)))), K3 H HH p»
            ] (refl …)
          ]  (refl bool (veqb (νy) (νx))) H1))≤ max (max (S x) (fresh_var_t t1)) (fresh_var_t t'))
      [5: #UU @UU | 1,2,3: skip ]
      lapply Hveqb >veqb_comm -Hveqb #Hveqb >Hveqb
      cut (fvb_t (νx) t' = true ∨ fvb_t (νx) t' = false) // * #Hfvbxt'
      >Hfvbxt'
      [ >Hfvb #K #K1 #K2 #K3
        normalize
        change with (max (S x) ?) in match (if ? then ? else S x);
        change with (max ? ?) in match (if ? then ? else (max ? ?));
        change with (fresh_var_t t1 )
          in match (pi1 ? ? (fresh_var_t_Sig t1 ));
        @le_n_max_n
      | #K #K1 #K2 #K3 normalize
        change with (max (S x) ?) in match (if ? then ? else S x);
        change with (pif_subst ? (psubst (νy) t')) in match ((pi1 pifTerm ?
        (pif_subst_sig (t_size t1) (νy) t' t1 (le_n (t_size t1)))));
        change with (fresh_var_t ?) in match (pi1 ? ?
          (fresh_var_t_Sig (pi1 pifTerm ? (pif_subst_sig ? (νy) t' t1 ?))));
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
        |
          cut (∀H. fresh_var_t (pi1 pifTerm ? (pif_subst_sig n (νy) t' t1 H)) ≤
          max (max (S x) (fresh_var_t t1)) (fresh_var_t t'))
          [ 2: #jj @jj ]
          cut (∀H. fresh_var_t (pi1 pifTerm ? (pif_subst_sig n (νy) t' t1 H)) ≤
               max (fresh_var_t t1) (fresh_var_t t'))
          [ #JJ @HI lapply H normalize cases neqb normalize #H destruct //
          | #Hm cut (max (fresh_var_t t1) (fresh_var_t t') ≤
                     max (max (S x) (fresh_var_t t1)) (fresh_var_t t'))
            [ //
            | #Hm2 #hh @(transitive_le … (Hm hh) Hm2) 
            ]
          ]
        ]
      ]
    ]
  ]
| #t1 #t2 #y #t' #H
  whd in match (fresh_var_t (appl ? ?));
  whd in match (pif_subst_sig ? ? ? (appl t1 t2) ?);
  whd in match (fresh_var_t (appl t1 t2));
  change with (fresh_var_t (pi1 pifTerm ? (pif_subst_sig n y t' t1 (subst_aux_10 t1 t2 n H))))
    in match (pi1 ? ? (fresh_var_t_Sig (pi1 pifTerm ?
    (pif_subst_sig n y t' t1 (subst_aux_10 t1 t2 n H)))));
  change with (fresh_var_t (pi1 pifTerm ? (pif_subst_sig n y t' t2 (subst_aux_9 t1 t2 n H))))
    in match (pi1 ? ? (fresh_var_t_Sig (pi1 pifTerm ?
    (pif_subst_sig n y t' t2 (subst_aux_9 t1 t2 n H)))));
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
  cut ((max (fresh_var_t (pi1 pifTerm ? (pif_subst_sig n y t' t1 (subst_aux_10 t1 t2 n H))))
            (fresh_var_t (pi1 pifTerm ? (pif_subst_sig n y t' t2 (subst_aux_9 t1 t2 n H)))) ≤
        max (max (fresh_var_t t1) (fresh_var_t t'))
            (max (fresh_var_t t2) (fresh_var_t t'))))
  [ @to_max
    [ cut (max (fresh_var_t t1) (fresh_var_t t') ≤
           max (max (fresh_var_t t1) (fresh_var_t t'))
                (max (fresh_var_t t2) (fresh_var_t t')))
      [ @le_n_max_n
      | #Hm @(transitive_le … (HI … Hin1) Hm)
      ]
    | cut (max (fresh_var_t t2) (fresh_var_t t') ≤
           max (max (fresh_var_t t1) (fresh_var_t t'))
                (max (fresh_var_t t2) (fresh_var_t t')))
      [ >(max_comm (max ? ?) ?) @le_n_max_n
      | #Hm @(transitive_le … (HI … Hin2) Hm)
      ]
    ]
  | #H //
] qed.

lemma fv_deletion0:
 (∀n,t,y,w,H. veqb y w = false → fvb_t y (pi1 … (pif_subst_sig n y (val_to_term (pvar w)) t H)) = false).

@nat_ind
[ *
  [ *
    [ #x #y #w #H @False_ind lapply H normalize /2/
    | #x #t #y #w #H @False_ind lapply H normalize /2/
    ]
  | #t1 #t2 #y #w #H @False_ind lapply H normalize /2/
  ]
]
#n #HI
* [ *
[ #x #y #w #Hs #H
  cut (veqb x y = true ∨ veqb x y = false) // * #Hxy
  [ elim (veqb_true_to_eq x y) #Heq #_ lapply (Heq Hxy) -Heq #Heq destruct
    >atomic_subst0 normalize >H normalize @refl
  | >no_subst0 normalize >veqb_comm >Hxy //
  ]
| #x #t1 #y #w #Hs #H
  cut (veqb x y = true ∨ veqb x y = false) // * #Hxy
  [ elim (veqb_true_to_eq x y) #Heq #_ lapply (Heq Hxy) -Heq #Heq destruct
    >no_subst20 normalize >veqb_true //
  | cut (∀ AAA,BBB,CCC,DDD. (fvb_t y
  (pi1 pifTerm
   (λu:pifTerm
    .t_size u
     =t_size (val_to_term (abstr x t1))
      +free_occ_t y (val_to_term (abstr x t1))*(t_size (val_to_term (pvar w))-1)
     ∧(∀z:Variable
       .free_occ_t z u
        =if veqb y z 
         then free_occ_t z (val_to_term (abstr x t1))
                  *free_occ_t z (val_to_term (pvar w)) 
         else free_occ_t y (val_to_term (abstr x t1))
                  *free_occ_t z (val_to_term (pvar w))
                  +free_occ_t z (val_to_term (abstr x t1)) ))
  (match veqb y x return λb. veqb y x = b → t_size (val_to_term (abstr x t1)) ≤ S n → Σu: pifTerm. (t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_v y (abstr x t1)) * ((t_size (val_to_term (pvar w))) - 1) ∧
        (∀z. free_occ_t z u = match veqb y z with
          [ true ⇒ (free_occ_v z (abstr x t1)) * (free_occ_t z (val_to_term (pvar w)))
          | false ⇒ (free_occ_v y (abstr x t1)) * (free_occ_t z (val_to_term (pvar w))) + (free_occ_v z (abstr x t1))
          ]))
       with
        [ true ⇒ λH.λp. « (val_to_term (abstr x t1)), AAA H p»
        | false ⇒ λH. match fvb_t x (val_to_term (pvar w)) return λb. fvb_t x (val_to_term (pvar w))=b → t_size (val_to_term (abstr x t1)) ≤ S n → Σu: pifTerm. (t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_v y (abstr x t1)) * ((t_size (val_to_term (pvar w))) - 1) ∧
          (∀z. free_occ_t z u = match veqb y z with
            [ true ⇒ (free_occ_v z (abstr x t1)) * (free_occ_t z (val_to_term (pvar w)))
            | false ⇒ (free_occ_v (y) (abstr x t1)) * (free_occ_t z (val_to_term (pvar w))) + (free_occ_v z (abstr x t1))
            ]))
         with
          [ true ⇒ λHH. match fvb_t y (val_to_term (abstr x t1)) return λHfvb. fvb_t y (val_to_term (abstr x t1)) = Hfvb →  t_size (val_to_term (abstr x t1)) ≤ S n → Σu: pifTerm. ((t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_t y (val_to_term (abstr x t1))) * ((t_size (val_to_term (pvar w))) - 1)) ∧
            (∀z. free_occ_t z u = match veqb y z with
               [ true ⇒ (free_occ_t z (val_to_term (abstr x t1))) * (free_occ_t z (val_to_term (pvar w)))
               | false ⇒ (free_occ_t y (val_to_term (abstr x t1))) * (free_occ_t z (val_to_term (pvar w))) + (free_occ_t z (val_to_term (abstr x t1)))
               ]))
             with
            [ true ⇒ λHfv.λp. let z ≝ (max (S match y with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t1) (fresh_var_t (val_to_term (pvar w))))))
                   in match (pif_subst_sig n x (val_to_term (pvar ν(z))) t1 ?) with
               [ mk_Sig a h ⇒ « (val_to_term (abstr (ν(z)) (pi1 … (pif_subst_sig n y (val_to_term (pvar w)) a (subst_aux_5 … h p))))), DDD H HH Hfv p a h »]
            | false ⇒ λHfv. λp. « (val_to_term (abstr x t1)), BBB H HH Hfv p »
            ] (refl …)
          | false ⇒ λHH. λp. « (val_to_term (abstr x (pi1 … (pif_subst_sig n y (val_to_term (pvar w)) t1 ?)))), CCC H HH p »
          ] (refl …)
        ]  (refl …) ?))
  =false))
  [ 5: #UU @UU | 1,2,3: skip ]
  cut (veqb y x = false) [ >veqb_comm // ] #Hyx
  >Hyx 
  cut (fvb_t x (val_to_term (pvar w)) = true ∨ fvb_t x (val_to_term (pvar w)) = false) // * #Hfv
  >Hfv
  [ 2: #AAA #BBB #CCC #DDD normalize >Hyx normalize @HI // ]
  cut (fvb_t y (val_to_term (abstr x t1))= true ∨ fvb_t y (val_to_term (abstr x t1))= false) // * #Hfv2
  >Hfv2
  [ 2: #AAA #BBB #CCC #DDD lapply Hfv2 normalize >Hyx >if_f // ]
  cases x in Hxy Hyx H ⊢%; #nx
  cases y #ny
  cases w #nw #Hxy #Hyx #H #AAA #BBB #CCC #DDD 
  whd in match (match ? in Variable with [_⇒ ?]);
  whd in match (match ? in Variable with [_⇒ ?]);
  whd in match (match ? in Variable with [_⇒ ?]);
  cases (pif_subst_sig n νnx) [ 2: /2/] #a #h
  cut (∀KKK. (fvb_t (νny)
  (pi1 pifTerm ?
   (( «val_to_term  (abstr (ν(?)) (pi1 pifTerm ? (pif_subst_sig ? (νny)
                                               (val_to_term (pvar νnw)) a KKK))),
                                           DDD (refl …) (refl …) (refl …) ? a h»)))
  =false)) //
  [ 2: #UUU @UUU ]
   #KKK
   whd in match (match ?  in Variable with [_⇒?]);
   whd in match (match ?  in Variable with [_⇒?]);
   change with (gtb (free_occ_t (νny) ?) 0) in match (fvb_t (νny) ?);
     whd in match (free_occ_t ? ?);
     whd in match (veqb ??);
     >neqb_x_max_Sx >if_f
     change with ((fvb_t (νny) ?)=false)
     >(HI a) //
   ]
]
| #t1 #t2 #y #w #Hs #H 
  whd in match (pif_subst_sig (S n) y (val_to_term (pvar w)) (appl t1 t2) ?);
  whd in match (fvb_t y ?);
  whd in match (free_occ_t y ?);
  lapply (HI t1 y w (subst_aux_10 t1 t2 … Hs) H)
  lapply (HI t2 y w (subst_aux_9 t1 t2 … Hs) H)
  whd in match (fvb_t y ?);
  whd in match (fvb_t y (pi1 pifTerm ? (pif_subst_sig ? ? ? t1 ?)));
  cases free_occ_t
  [ whd in match (gtb 0 0); #_
    cases (free_occ_t y …) /2/
  | #n whd in match (gtb (S n) 0); #abs destruct
  ]
] qed.

definition pif_subst ≝ λt.λs. pi1 … (pif_subst_sig (t_size t) match s with [psubst y t' ⇒ y] match s with [psubst y t' ⇒ t'] t ?).// qed.
definition pif_subst_v ≝ λv.λs. pi1 … (pif_subst_sig (t_size (val_to_term v)) match s with [psubst y t' ⇒ y] match s with [psubst y t' ⇒ t'] (val_to_term v) ?).// qed.

lemma pif_subst_distro:
 ∀t1, t2, s. pif_subst (appl t1 t2) s = appl (pif_subst t1 s) (pif_subst t2 s).

#t1 #t2 * #y #t'
change with (pi1 … (pif_subst_sig (t_size (appl t1 t2)) y t' (appl t1 t2) ?)) in match (pif_subst (appl t1 t2) (psubst y t'));
change with (pi1 … (pif_subst_sig (t_size t1) y t' t1 ?)) in match (pif_subst t1 (psubst y t'));
change with (pi1 … (pif_subst_sig (t_size t2) y t' t2 ?)) in match (pif_subst t2 (psubst y t'));
change with (S ((t_size t1) + (t_size t2))) in match (t_size (appl t1 t2));
@pif_subst_distro0 qed.

lemma atomic_subst: ∀x, t. (pif_subst (val_to_term (pvar x)) (psubst x t)) = t.
#x #t
change with (pi1 pifTerm ? (pif_subst_sig …)) in match (pif_subst ? ?);
whd in match (match ? in pifSubst with [_⇒?]);
whd in match (match ? in pifSubst with [_⇒?]);
@atomic_subst0 qed.

lemma no_subst: ∀y,x,t'.
 veqb x y = false →
  (pif_subst (val_to_term (pvar y)) (psubst x t') ) = (val_to_term (pvar y)).
#y #x #t' @no_subst0 qed.

lemma no_subst2: ∀x, t, u. pif_subst (val_to_term (abstr x t)) (psubst x u) = (val_to_term (abstr x t)).
#x #t1 #t' @no_subst20 qed.

lemma abstr_step_subst: ∀x, y, t1, t'.
 veqb y x =false →
  fvb_t x t' = false →
   pif_subst (val_to_term (abstr x t1)) (psubst y t') = (val_to_term (abstr x (pif_subst t1 (psubst y t')))).

 #x #y #t1 #t' #Hveq #Hfv
 change with (pi1 … (pif_subst_sig …)) in match (pif_subst (val_to_term (abstr x t1)) (psubst y t'));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);
 >abstr_step_subst0 // [ 2: normalize @le_S @le_n] @eq_f @eq_f /2/ qed.

lemma no_subst5:
 (∀t,y,t'. fvb_t (νy) t =false → pif_subst t (psubst (νy) t')=t).
#t #y #t' #H
change with (pi1 … (pif_subst_sig …)) in match (pif_subst ? (psubst ? t'));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);
@no_subst50 @H qed.

lemma no_subst3:
 (∀t,y,t'. inb_t (νy) t =false → pif_subst t (psubst (νy) t')=t).
 
#t #y #t' #H
change with (pi1 … (pif_subst_sig …)) in match (pif_subst ? (psubst ? t'));
whd in match (match ? in pifSubst with [_ ⇒ ?]);
whd in match (match ? in pifSubst with [_ ⇒ ?]);
@no_subst30 @H qed.

lemma fresh_var_pif_subst:
 (∀t, y, t'. inb_t y t=false →
  fresh_var_t (pif_subst t (psubst y t')) ≤ max (fresh_var_t t) (fresh_var_t t')).

#t #y #t' @fresh_var_pif_subst0 qed.

(*
lemma s_pifsubst:
 (∀t,x,y,t'. fresh_var_t t ≤ y → fresh_var_t t' ≤ y →
   pif_subst (pif_subst t (psubst x (val_to_term (pvar (νy))))) (psubst (νy) t') =
    pif_subst t (psubst x t')) ∧
  (∀v,x,y,t'. fresh_var_tv v ≤ y → fresh_var_t t' ≤ y →
    pif_subst (pif_subst (val_to_term v) (psubst x (val_to_term (pvar (νy))))) (psubst (νy) t') =
     pif_subst (val_to_term v) (psubst x t')).

@pifValueTerm_ind
[ #v #H @H
| #t1 #t2 #H1 #H2 * #x #y #t' #H change with (max ? ? ≤y) in H;
  cut (pif_subst (appl t1 t2) (psubst (νx) (val_to_term (pvar νy)))=
       appl (pif_subst t1 (psubst (νx) (val_to_term (pvar νy))))
            (pif_subst t2 (psubst (νx) (val_to_term (pvar νy))))) // #Ht >Ht -Ht
  >pif_subst_distro >pif_subst_distro #H'
  >(H1 … (le_maxl … H) H') >(H2 … (le_maxr … H) H') //
| * #z * #x #y #t #H
  cut (veqb (νz) (νy) =false)
  [ lapply H normalize cut (veqb (νz) (νy) =true ∨ veqb (νz) (νy) =false) // * //
    elim (veqb_true_to_eq (νz) (νy)) #Heq #_ #Hzy lapply (Heq Hzy) -Heq #Heq destruct
    #abs @False_ind @(le_Sn_n y) @abs
  | -H #H cut (veqb (νz) (νx)=true ∨ veqb (νz) (νx)=false) // * #Hzx
    [ elim (veqb_true_to_eq (νz) (νx)) #Heq #_ lapply (Heq Hzx) -Heq #Heq destruct
      >atomic_subst //
    | >no_subst // >no_subst //
      >no_subst //
    ]
  ]
| #t1 * #z #HI * #x #y #t' #Ha #Hb change with (max ? ?≤y) in Ha;
  lapply (HI (νx) y  t' (le_maxr … Ha)) #HI'
  cut (veqb (νx) (νz) =true ∨ veqb (νx) (νz) = false) // * #Hxz
  [ elim (veqb_true_to_eq (νx) (νz)) #Heq #_ lapply (Heq Hxz) -Heq #Heq destruct
    >no_subst2 >no_subst2
    cut (veqb (νy) (νz) =true ∨ veqb (νy) (νz) = false) // * #Hyz
    [ elim (veqb_true_to_eq (νy) (νz)) #Heq #_ lapply (Heq Hyz) -Heq #Heq destruct
      >no_subst2 //
    | lapply (no_subst4) * #Hns #_ >Hns //
      lapply (fresh_var_to_in) * #Hfvtoin #_
      change with (fresh_var_t (val_to_term (abstr (νz) ?))≤y) in Ha;
      lapply (Hfvtoin … Ha) -Hfvtoin #Hin
      lapply (fv_to_in_term) * #Hfvtoin #_
      cut (∀t:pifTerm.∀x:Variable.inb_t x t=false→fvb_t x t=false)
      [ #t #x lapply (Hfvtoin t x) cases fvb_t cases inb_t // #H #_ >H //]
      -Hfvtoin #Hfvtoin >Hfvtoin //
    ]
  | >abstr_step_subst
    [ 2: normalize lapply (le_maxl … Ha)
      cut (neqb z y = true ∨ neqb z y = false) // * #Hzy >Hzy normalize //
       elim (neqb_iff_eq (z) (y)) #Heq #_ lapply (Heq Hzy) -Heq #Heq destruct
       #abs @False_ind @(le_Sn_n y) @abs
    | 3: @Hxz
    ]
    >abstr_step_subst
    [ >(HI' Hb) >abstr_step_subst // lapply (le_maxl … Ha)
    [ 2:
    | 3: normalize lapply (le_maxl … H)
      cut (neqb z y = true ∨ neqb z y = false) // * #Hzy >Hzy normalize //
       elim (neqb_iff_eq (z) (y)) #Heq #_ lapply (Heq Hzy) -Heq #Heq destruct
       #abs @False_ind @(le_Sn_n y) @abs
    ]
  [ 2:
  cut (fvb_t ν)
  (*z≠y*)
*)

lemma pif_subst_same_size0:
 (∀n,t,y,w,H.
  t_size (pi1 pifTerm ? (pif_subst_sig n y (val_to_term (pvar w)) t H)) =
  t_size t).

#n #t #y #w #H

@sigma_prop_gen #z #z_def * #Hs #_ >Hs normalize // qed.
(*
lemma subst_union0:
 (∀n,t,y,w,t',H1,H2,H3.
  inb_t w t = false →
  pi1 pifTerm ? (pif_subst_sig n w t' (pi1 pifTerm ? (pif_subst_sig n y (val_to_term (pvar w)) t H1)) H2) =
   pi1 pifTerm ? (pif_subst_sig n y t' t H3)).
@nat_ind
[ *
  [ *
    [ #x #y #w #t #H @False_ind lapply H normalize /2/
    | #x #t #y #w #t #H @False_ind lapply H normalize /2/
    ]
  | #t1 #t2 #t' #y #w #t #H @False_ind lapply H normalize /2/
  ]
]
#n #HI *
[ *
  [ #x #y #w #t' #H1 #H2 #H3 #H
    cut (veqb y x = true ∨ veqb y x = false) // * #Hyx
    [ elim (veqb_true_to_eq y x) #Heq #_ lapply (Heq Hyx) -Heq #Heq destruct
      >(atomic_subst0 (S n) x t')
      >(atomic_subst0 (S n) x (val_to_term (pvar w)) H1) in H2 H3 ⊢%;
      #H2 #H3
      >atomic_subst0 //
    | >(no_subst0 (S n) y x t') //
      >(no_subst0 (S n) y x (val_to_term (pvar w)) H1) in H2 H3 ⊢ %; //
      >no_subst0 // lapply H normalize cases veqb //
    ]
  | #x #t1 #y #w #t' #H1 #H2 #H3 #H
    cut (veqb y x = true ∨ veqb y x = false) // * #Hyx
    [ elim (veqb_true_to_eq y x) #Heq #_ lapply (Heq Hyx) -Heq #Heq destruct
      >(no_subst20 ? x t1) in H2 H3 ⊢%; #H2 #H3
      >no_subst20
      lapply no_subst5 * #H5 #_ @(H5)
      lapply H normalize cases veqb // >if_f >if_f
      lapply (fv_to_in_term) * #Ht #_
      cut (∀t:pifTerm.∀x0:Variable.inb_t x0 t=false→fvb_t x0 t=false)
      [ #t #x lapply (Ht t x) cases fvb_t // cases inb_t // #H #_ >H // ]
      -Ht #Ht #HH @Ht @HH
    | >abstr_step_subst0 in H2 ⊢% ; //
      [ 2: lapply H normalize >veqb_comm cases veqb // >if_t #abs destruct ]
      [ 2: lapply H1 normalize /2/ ]
      #H2
      cut (fvb_t x t' = true ∨ fvb_t x t' = false) // * #Hfvt
      [ 2: >abstr_step_subst0 in H2 ⊢% ; //
        [ 2: lapply H normalize cases veqb // >if_t //
        | 3: >pif_subst_same_size0 lapply H1 normalize /2/
        | 4: whd in match (t_size (val_to_term (abstr x ?)));
          >pif_subst_same_size0 lapply H1 normalize /2/ ]
        #H2 >abstr_step_subst0 in H2 ⊢% ; // [ 2: lapply H1 normalize /2/ ]
        #H2 @eq_f @eq_f2 //
        cut (∀K, K1, K2. (pi1 pifTerm ?
          (pif_subst_sig (S n) w t'
          (pi1 pifTerm ? (pif_subst_sig (S n) y (val_to_term (pvar w)) t1 K)) K1)
  =pi1 pifTerm ?
   (pif_subst_sig (S n) y t' t1  K2)))
     [ 2: #UU @UU ] #K #K1 #K2
        >(pif_subst_bound_irrelevance ? n t1 y t') [ 2: lapply H1 normalize /2/ ]
        >(pif_subst_bound_irrelevance ? n t1 y (val_to_term (pvar w))) in K1 ⊢%;
        [ 2: lapply H1 normalize /2/ ] #K1
        >(pif_subst_bound_irrelevance (S n) n ? w t') in K1 ⊢%;
        [ 2: >pif_subst_same_size0 lapply H1 normalize /2/
        | 3: >pif_subst_same_size0 // ] #K1 @HI lapply H
        normalize cases veqb  cases inb_t // normalize #H @H ]
      ]

  ]
| #t1 #t2 #y #w #t' #H1 #H2 #H3 #H
  whd in match (pif_subst_sig ? ? ? (appl t1 t2) ?);
  whd in match (pif_subst_sig ? ? ? (appl (pi1 pifTerm ? ?) (pi1 pifTerm ? ?)) ?);
  @eq_f2 @HI lapply H normalize cases free_occ_t // #n normalize // #abs destruct
]

lemma teripp_lemma:
 (∀t, u, x, y, z.
  inb_t y t = false →
   inb_t y u = false → veqb y z = false → veqb y x = false →
    veqb x z = false →
       (pif_subst (pif_subst t (psubst x (val_to_term (pvar y))))
        (psubst z (pif_subst u (psubst x (val_to_term (pvar y))))) =
         pif_subst (pif_subst t (psubst z u)) (psubst x (val_to_term (pvar y))))) ∧
(∀v, u, x, y, z.
  inb_tv y v = false →
   inb_t y u = false →
    veqb y z = false →
     veqb y x = false → veqb x z = false →
       (pif_subst (pif_subst (val_to_term v) (psubst x (val_to_term (pvar y))))
        (psubst z (pif_subst u (psubst x (val_to_term (pvar y))))) =
         pif_subst (pif_subst (val_to_term v) (psubst z u)) (psubst x (val_to_term (pvar y))))).

@pifValueTerm_ind
[ #v #H @H
| #t1 #t2 #Ht1 #Ht2 #u #x #y #z #H1 #H2 #H3 #H4 #H5
  >pif_subst_distro
  whd in match (match ? in pifSubst with [_⇒?]);
  whd in match (match ? in pifSubst with [_⇒?]);
  whd in match (match ? in pifSubst with [_⇒?]);
  >pif_subst_distro
  whd in match (match ? in pifSubst with [_⇒?]);
  whd in match (match ? in pifSubst with [_⇒?]);
  @eq_f2
  [ >(pif_subst_bound_irrelevance ((t_size t1)+(t_size t2)) (t_size t1)) //
    [ 2: //]
     >(pif_subst_bound_irrelevance ((t_size t1)+(t_size t2)) (t_size t1)) //
    [ 2: //] >Ht1 //
    lapply H1 normalize cases inb_t normalize //
  | >(pif_subst_bound_irrelevance ((t_size t1)+(t_size t2)) (t_size t2)) //
    [ 2: //]
     >(pif_subst_bound_irrelevance ((t_size t1)+(t_size t2)) (t_size t2)) //
    [ 2: //] >Ht2 //
    lapply H1 normalize cases (inb_t ? t2) normalize // >if_monotone #H @H
  ]
| #x #u #y #w #z #H1 #H2 #H3 #H4 #H5
  cut (veqb y x = true ∨ veqb y x = false) // * #Hyx
  [ 2: >no_subst //
    cut (veqb z x = true ∨ veqb z x = false) // * #Hzx
    [ 2: >no_subst // >no_subst // >no_subst // ]
    elim (veqb_true_to_eq z x) #Heq #_ lapply (Heq Hzx) -Heq #Heq destruct
    >atomic_subst >atomic_subst //
  | elim (veqb_true_to_eq y x) #Heq #_ lapply (Heq Hyx) -Heq #Heq destruct
    >atomic_subst >no_subst [ 2: >veqb_comm //]
    >no_subst //
  ]
| #t #x #H #u #w #y #z #H1 #H2 #H3 #H4 #H5
  cut (veqb x w = true ∨ veqb x w = false) // * #Hxw
  [ elim (veqb_true_to_eq x w) #Heq #_ lapply (Heq Hxw) -Heq #Heq destruct
    >no_subst2
    >abstr_step_subst
    [ 2: lapply (teripp_aux1 (t_size u)) * #tat #_ @tat
      >veqb_comm  //
    | 3: >veqb_comm //
    ]
    whd in match ((pif_subst u (psubst w (val_to_term (pvar y)))));
    whd in match (match ? in pifSubst with [_⇒?]);
    whd in match (match ? in pifSubst with [_⇒?]);
    >abstr_step_subst
    [ 2: lapply (teripp_aux1 (t_size u)) * #tat #_ @tat
      >veqb_comm  //
    | 3: >veqb_comm //
    ]
    cut (fvb_t w u=true ∨ fvb_t w u=false) // * #Hwu
    [ 2: >(abstr_step_subst) //
      >no_subst2 @eq_f @eq_f2 //
      lapply no_subst5 * #Hns #_ >Hns // ]
    >H
    whd in match ((pif_subst (val_to_term (abstr w t)) (psubst z u)));
    whd in match (match ? in pifSubst with [_⇒?]);
    whd in match (match ? in pifSubst with [_⇒?]);
    >(abstr_step_subst
    [ 2: lapply (teripp_aux1 (t_size u)) * #tat #_ @tat
      >veqb_comm  //
    | 3: >veqb_comm //
    ]
    whd in match ((pif_subst (val_to_term (abstr w t)) (psubst z u)));
    whd in match (match ? in pifSubst with [_⇒?]);
    whd in match (match ? in pifSubst with [_⇒?]);
    >abstr_step_subst
    [ 2: lapply (teripp_aux1 (t_size u)) * #tat #_ @tat
      >veqb_comm  //
    | 3: >veqb_comm //
    ]
    >abstr_step_subst
    >(no_subst2 w )
    [
    whd in match (pif_subst (val_to_term (abstr w t)) (psubst ? (pi1 …)));
    whd in match (match psubst z (pi1 pifTerm ?
                   (pif_subst_sig (t_size u) w (val_to_term (pvar y)) u
                    ?))
                   with 
                  [psubst y t⇒t]);
    whd in match (match 
             psubst z
             (pi1 pifTerm ?
              (pif_subst_sig (t_size u) w (val_to_term (pvar y)) ??))
              with 
             [psubst y t⇒y]);
    whd in match (match ? in pifSubst return λ_:pifSubst.Variable with [_⇒?]);
    whd in match (match ? in pifSubst return λ_:pifSubst.Variable with [_⇒?]);





  whd in match (pif_subst (val_to_term (pvar ?)) (psubst ? (val_to_term (pvar ?))));
  whd in match (match ?  in pifSubst with [_⇒?]);
  whd in match (match ?  in pifSubst with [_⇒?]);
  whd in match ((pif_subst_sig (t_size (val_to_term (pvar ?))) ? (val_to_term (pvar ?))
    (val_to_term (pvar ?)) (le_n (t_size (val_to_term (pvar ?))))));
  cut (veqb y x = true ∨ veqb x y = false) // * #Hyx
  [ 2: >(no_subst y x) //
  whd in match (match psubst y (val_to_term (pvar w))
                  in pifSubst
                  return λ_:pifSubst.pifTerm
                  with 
                 [psubst (x0:Variable)   (t0:pifTerm)⇒t0]);
 cut ( ∀AA,BB. (pif_subst
  (pi1 pifTerm
   (λu0:pifTerm
    .t_size u0
     =t_size (val_to_term (pvar x))
      +free_occ_t y (val_to_term (pvar x))*(t_size (val_to_term (pvar w))-1)
     ∧(∀z0:Variable
       .free_occ_t z0 u0
        =if veqb y z0 
         then free_occ_t z0 (val_to_term (pvar x))
                  *free_occ_t z0 (val_to_term (pvar w)) 
         else free_occ_t y (val_to_term (pvar x))
                  *free_occ_t z0 (val_to_term (pvar w))
                  +free_occ_t z0 (val_to_term (pvar x)) ))
   (match veqb y x return λb.  veqb y x = b → t_size (val_to_term (pvar x)) ≤ 1 → Σu: pifTerm. (t_size u = (t_size (val_to_term (pvar x)))+ (free_occ_v y (pvar x)) * ((t_size (val_to_term (pvar w))) - 1) ∧
        (∀z. free_occ_t z u = match veqb y z with
          [ true ⇒ (free_occ_v z (pvar x)) * (free_occ_t z  (val_to_term (pvar w)))
          | false ⇒ (free_occ_v y (pvar x)) * (free_occ_t z (val_to_term (pvar w))) + (free_occ_v z (pvar x))
          ]))
        with
         [true ⇒λH.λp.«val_to_term (pvar w), AA H p» | false ⇒ λH.λp.«val_to_term (pvar x), BB H p»] (refl …) (le_n (t_size (val_to_term (pvar x)))))))
           (psubst z (pif_subst u (psubst y (val_to_term (pvar w)))))
  =pif_subst (pif_subst (val_to_term (pvar x)) (psubst z u))
   (psubst y (val_to_term (pvar w))))
 [2: #UU @UU]
  #AA #BB cut (veqb y x = true ∨ veqb x y = false) // *
*)
