include "crumbles.ma".
include "basics/types.ma".
include "libnat.ma".
include "variables.ma".
include "utils.ma".
include "size.ma".

lemma p_subst_aux1: (∀t. S (t_size t -1)=t_size t) ∧ (∀v. S (v_size v -1)=v_size v).
@pValueTerm_ind
[ #v #H normalize //
| #t1 #t2 #H1 #H2 normalize //
| #x normalize //
| #t #x #H normalize //]
qed.

(*
lemma generalize_sigma_prop_gen:
 ∀n,s,p,P.
  (∀q. P (p_subst n s t q)) →
    P (p_subst n s t p).
*)

lemma subst_aux_1:
 ∀ s, t.
  t_size t≤O
     →Σu:pTerm
      .t_size u
       =t_size t
        +free_occ_t
         match s in pSubst return λ_:pSubst.Variable with 
         [psubst (x:Variable)   (t0:pTerm)⇒x] t
         *(t_size
           match s in pSubst return λ_:pSubst.pTerm with 
           [psubst (x:Variable)   (t0:pTerm)⇒t0]
           -1)
       ∧(∀z:Variable
         .free_occ_t z u
          =if veqb
                match s in pSubst return λ_:pSubst.Variable with 
                [psubst (y:Variable)   (t':pTerm)⇒y] z 
           then free_occ_t z t
                    *free_occ_t z
                     match s in pSubst return λ_:pSubst.pTerm with 
                     [psubst (y:Variable)   (t':pTerm)⇒t'] 
           else free_occ_t
                    match s in pSubst return λ_:pSubst.Variable with 
                    [psubst (y:Variable)   (t':pTerm)⇒y] t
                    *free_occ_t z
                     match s in pSubst return λ_:pSubst.pTerm with 
                     [psubst (y:Variable)   (t':pTerm)⇒t']
                    +free_occ_t z t ).


#s #t
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
               *free_occ_t z
                match psubst y t' in pSubst return λ_:pSubst.pTerm with 
                [psubst (y0:Variable)   (t':pTerm)⇒t'] 
      else free_occ_v
               match psubst y t' in pSubst return λ_:pSubst.Variable with 
               [psubst (y0:Variable)   (t':pTerm)⇒y0]
               (pvar x)
               *free_occ_t z
                match psubst y t' in pSubst return λ_:pSubst.pTerm with 
                [psubst (y0:Variable)   (t':pTerm)⇒t']
               +free_occ_v z (pvar x) )).

#t' #x #y #m #H #p
normalize in p; normalize >H normalize <(plus_n_O (t_size t' -1))
lapply(p_subst_aux1) * #H1 #_ >(H1 t') % //
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
   +free_occ_v
    match psubst y t' in pSubst return λ_:pSubst.Variable with 
    [psubst (x0:Variable)   (t0:pTerm)⇒x0] (pvar x)
    *(t_size
      match psubst y t' in pSubst return λ_:pSubst.pTerm with 
      [psubst (x0:Variable)   (t0:pTerm)⇒t0]
      -1)
  ∧(∀z:Variable
    .free_occ_t z (val_to_term (pvar x))
     =if veqb
           match psubst y t' in pSubst return λ_:pSubst.Variable with 
           [psubst (y0:Variable)   (t':pTerm)⇒y0] z 
      then free_occ_v z (pvar x)
               *free_occ_t z
                match psubst y t' in pSubst return λ_:pSubst.pTerm with 
                [psubst (y0:Variable)   (t':pTerm)⇒t'] 
      else free_occ_v
               match psubst y t' in pSubst return λ_:pSubst.Variable with 
               [psubst (y0:Variable)   (t':pTerm)⇒y0]
               (pvar x)
               *free_occ_t z
                match psubst y t' in pSubst return λ_:pSubst.pTerm with 
                [psubst (y0:Variable)   (t':pTerm)⇒t']
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
 ∀ t1,x,s,  m.
   (veqb
   match s in pSubst return λ_:pSubst.Variable with 
   [psubst (x0:Variable)   (t0:pTerm)⇒x0] x
   =true) →
    (t_size (val_to_term (abstr x t1))≤S m)→
 (t_size (val_to_term (abstr x t1))
  =t_size (val_to_term (abstr x t1))
   +free_occ_v
    match s in pSubst return λ_:pSubst.Variable with 
    [psubst (x0:Variable)   (t0:pTerm)⇒x0] (abstr x t1)
    *(t_size
      match s in pSubst return λ_:pSubst.pTerm with 
      [psubst (x0:Variable)   (t0:pTerm)⇒t0]
      -1)
  ∧(∀z:Variable
    .free_occ_t z (val_to_term (abstr x t1))
     =if veqb
           match s in pSubst return λ_:pSubst.Variable with 
           [psubst (y:Variable)   (t':pTerm)⇒y] z 
      then free_occ_v z (abstr x t1)
               *free_occ_t z
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t'] 
      else free_occ_v
               match s in pSubst return λ_:pSubst.Variable with 
               [psubst (y:Variable)   (t':pTerm)⇒y] (abstr x t1)
               *free_occ_t z
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t']
               +free_occ_v z (abstr x t1) )).

#t1 #x #s #m #H #_

lapply H cases s #y #t' normalize #H1 >H1 normalize % //
  lapply (veqb_true_to_eq y x) * #Heq #_ lapply (Heq H1) -Heq #Heq destruct
  #z lapply (veqb_comm x z) #Hcomm >Hcomm -Hcomm cases (veqb z x) normalize //

qed.

lemma subst_aux_5: ∀t1, x, z, a, m.

(t_size a
   =t_size t1
    +free_occ_t
     match psubst x (val_to_term (pvar νz))
      in pSubst
      return λ_:pSubst.Variable
      with 
     [psubst (x0:Variable)   (t0:pTerm)⇒x0] t1
     *(t_size
       match psubst x (val_to_term (pvar νz))
        in pSubst
        return λ_:pSubst.pTerm
        with 
       [psubst (x0:Variable)   (t0:pTerm)⇒t0]
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 a
      =if veqb
            match psubst x (val_to_term (pvar νz))
             in pSubst
             return λ_:pSubst.Variable
             with 
            [psubst (y:Variable)   (t':pTerm)⇒y] z0 
       then free_occ_t z0 t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar νz))
                  in pSubst
                  return λ_:pSubst.pTerm
                  with 
                 [psubst (y:Variable)   (t':pTerm)⇒t'] 
       else free_occ_t
                match psubst x (val_to_term (pvar νz))
                 in pSubst
                 return λ_:pSubst.Variable
                 with 
                [psubst (y:Variable)   (t':pTerm)⇒y] t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar νz))
                  in pSubst
                  return λ_:pSubst.pTerm
                  with 
                 [psubst (y:Variable)   (t':pTerm)⇒t']
                +free_occ_t z0 t1 )) →
                (t_size (val_to_term (abstr x t1))≤S m) →
                t_size a ≤ m.

#t1 #x #z #a #m #h #p
normalize in h; lapply h * -h #h #_ normalize in p; /2/
qed.

lemma p_subst_aux_6:
∀( n : ℕ).
∀( s : pSubst).
∀( m : ℕ).
∀( t : pTerm).
∀( v : pValue).
∀( x : Variable).
∀( t1 : pTerm).
∀( H :
  (veqb
   match s in pSubst return λ_:pSubst.Variable with 
   [psubst (x0:Variable)   (t0:pTerm)⇒x0] x
   =false)).
∀( HH :
  (fvb_t x
   match s in pSubst return λ_:pSubst.pTerm with 
   [psubst (x0:Variable)   (t0:pTerm)⇒t0]
   =true)).
∀( p : (t_size (val_to_term (abstr x t1))≤S m)).
∀( z : ℕ).
∀( hz: z =
  (max
   (S
    match s in pSubst return λ_:pSubst.ℕ with 
    [psubst (x0:Variable)   (t0:pTerm)⇒
     match x0 in Variable return λ_:Variable.ℕ with [variable (n0:ℕ)⇒n0]])
   (max (S match x in Variable return λ_:Variable.ℕ with [variable (nx:ℕ)⇒nx])
    (max (fresh_var_t t1)
     (fresh_var_t
      match s in pSubst return λ_:pSubst.pTerm with 
      [psubst (x0:Variable)   (t0:pTerm)⇒t0]))))).
∀( a : pTerm).
∀( h :
  (t_size a
   =t_size t1
    +free_occ_t
     match psubst x (val_to_term (pvar (νz)))
      in pSubst
      return λ_:pSubst.Variable
      with 
     [psubst (x0:Variable)   (t0:pTerm)⇒x0] t1
     *(t_size
       match psubst x (val_to_term (pvar νz))
        in pSubst
        return λ_:pSubst.pTerm
        with 
       [psubst (x0:Variable)   (t0:pTerm)⇒t0]
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 a
      =if veqb
            match psubst x (val_to_term (pvar (νz)))
             in pSubst
             return λ_:pSubst.Variable
             with 
            [psubst (y:Variable)   (t':pTerm)⇒y] z0 
       then free_occ_t z0 t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar (νz)))
                  in pSubst
                  return λ_:pSubst.pTerm
                  with 
                 [psubst (y:Variable)   (t':pTerm)⇒t'] 
       else free_occ_t
                match psubst x (val_to_term (pvar (νz)))
                 in pSubst
                 return λ_:pSubst.Variable
                 with 
                [psubst (y:Variable)   (t':pTerm)⇒y] t1
                *free_occ_t z0
                 match psubst x (val_to_term (pvar (νz)))
                  in pSubst
                  return λ_:pSubst.pTerm
                  with 
                 [psubst (y:Variable)   (t':pTerm)⇒t']
                +free_occ_t z0 t1 ))).
∀( k : pTerm ).
∀( k_size :
  (t_size k
   =t_size a
    +free_occ_t
     match s in pSubst return λ_:pSubst.Variable with 
     [psubst (x0:Variable)   (t0:pTerm)⇒x0] a
     *(t_size
       match s in pSubst return λ_:pSubst.pTerm with 
       [psubst (x0:Variable)   (t0:pTerm)⇒t0]
       -1)
   ∧(∀z00:Variable
     .free_occ_t z00 k
      =if veqb
            match s in pSubst return λ_:pSubst.Variable with 
            [psubst (y:Variable)   (t':pTerm)⇒y] z00 
       then free_occ_t z00 a
                *free_occ_t z00
                 match s in pSubst return λ_:pSubst.pTerm with 
                 [psubst (y:Variable)   (t':pTerm)⇒t'] 
       else free_occ_t
                match s in pSubst return λ_:pSubst.Variable with 
                [psubst (y:Variable)   (t':pTerm)⇒y] a
                *free_occ_t z00
                 match s in pSubst return λ_:pSubst.pTerm with 
                 [psubst (y:Variable)   (t':pTerm)⇒t']
                +free_occ_t z00 a ))).

 (t_size (val_to_term (abstr (νz) k))
  =t_size (val_to_term (abstr x t1))
   +free_occ_v
    match s in pSubst return λ_:pSubst.Variable with 
    [psubst (x0:Variable)   (t0:pTerm)⇒x0] (abstr x t1)
    *(t_size
      match s in pSubst return λ_:pSubst.pTerm with 
      [psubst (x0:Variable)   (t0:pTerm)⇒t0]
      -1)
  ∧(∀z00:Variable
    .free_occ_t z00 (val_to_term (abstr (νz) k))
     =if veqb
           match s in pSubst return λ_:pSubst.Variable with 
           [psubst (y:Variable)   (t':pTerm)⇒y] z00 
      then free_occ_v z00 (abstr x t1)
               *free_occ_t z00
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t'] 
      else free_occ_v
               match s in pSubst return λ_:pSubst.Variable with 
               [psubst (y:Variable)   (t':pTerm)⇒y] (abstr x t1)
               *free_occ_t z00
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t']
               +free_occ_v z00 (abstr x t1) )).
#n #s #m #t #v #x #t1 #H #HH #p #z #z_def #a #h #k #k_size destruct

whd in match (t_size ?) in ⊢ %;
  whd in match (t_size (val_to_term ?)) in ⊢ %;
  lapply k_size * -k_size #k_size #k_fv >k_size lapply h -h * #a_size #a_fv >a_size lapply H
   normalize in a_fv; lapply a_fv lapply k_fv normalize cases s #y #t -k_fv #k_fv normalize
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
    [ lapply (Heq Hzx) -Heq #Heq destruct >(rifle_neqb … nx) normalize
      cut (neqb nx ny = true ∨neqb nx ny = false) // * #Hxy lapply (neqb_iff_eq nx ny) *
      #Heq2 #_
      [ lapply (Heq2 Hxy) -Heq2 #Heq2 destruct >Hxy >(rifle_neqb … ny) normalize
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb ny q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match ( match  max (S ny) (max (fresh_var_t t1) (fresh_var_t t)) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb ny q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        >(neqb_x_max_Sx ny (max (S ny) (max (fresh_var_t t1) (fresh_var_t t)))) normalize /2/
      | -Heq2 >(neq_simm ny nx) >Hxy normalize
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S nx) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb nx q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match ( match  max (S nx) (max (fresh_var_t t1) (fresh_var_t t)) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb ny q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        cut ( neqb nx (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t)))) = false)
        [ /2/ | #Hfalse >Hfalse normalize >Hfva /2/]
      ]
    | -Heq cut (neqb ny nww =true ∨ neqb ny nww = false) // * #Hyz >Hyz
      [ lapply (neqb_iff_eq ny nww) * #Heq #_ lapply (Heq Hyz) -Heq #Heq
        destruct normalize
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S nx) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb nx q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        change with (leb (S ?) ?) in match ( match  max (S nx) (max (fresh_var_t t1) (fresh_var_t t)) in nat return λ_:ℕ.bool
                 with [O⇒false|S (q:ℕ)⇒leb nww q]);
        change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
        cut ( neqb nww (max (S nww) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t)))) = false)
        [/2/ | #Hfalse >Hfalse normalize >(neq_simm nx nww) >Hzx normalize /2/]
      | lapply H -H #Hxy >(neq_simm ny nx) >(neq_simm nww ny) >(neq_simm nx nww) >Hxy >Hyz >Hzx normalize
          change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
          change with (leb (S nx) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb nx q]);
          change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
          change with (leb (S ?) ?) in match ( match  max (S nx) (max (fresh_var_t t1) (fresh_var_t t)) in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb ny q]);
          change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
          cut (neqb nww (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t))))=true ∨ neqb nww (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t))))=false)
          // * #Htf
          [ >Htf normalize lapply (neqb_iff_eq nww (max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t)))))
            * #Heq #_ lapply (Heq Htf) -Heq -Htf #Heq >Heq normalize
            change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
            change with (leb (S nx) ?) in match ( match max (fresh_var_t t1) (fresh_var_t t) in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb nx q]);
             change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
             change with (leb (S ?) ?) in match ( match  max (S nx) (max (fresh_var_t t1) (fresh_var_t t)) in nat return λ_:ℕ.bool
                   with [O⇒false|S (q:ℕ)⇒leb ny q]);
             change with (max ? ?) in match  (if leb ? ? then ? else ?) in ⊢ % ;
             >(max_comm (fresh_var_t t1) (fresh_var_t t)) in match ((free_occ_t (νny) t1)*free_occ_t (ν(max (S ny) (max (S nx) (max (fresh_var_t t1) (fresh_var_t t))))) t);
             >(max_swap (S nx) (fresh_var_t t) (fresh_var_t t1))
             >(max_swap (S ny) (fresh_var_t t) (max (S nx) (fresh_var_t t1)))
             >(max_swap (S nx) (fresh_var_t t1) (fresh_var_t t))
             >(max_swap (S ny) (fresh_var_t t1) (max (S nx) (fresh_var_t t)))
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
∀( n : ℕ).
∀( s : pSubst).
∀( m : ℕ).
∀( t : pTerm).
∀( v : pValue).
∀( x : Variable).
∀( t1 : pTerm).
∀( H :
  (veqb
   match s in pSubst return λ_:pSubst.Variable with 
   [psubst (x0:Variable)   (t0:pTerm)⇒x0] x
   =false)).
∀( HH :
  (fvb_t x
   match s in pSubst return λ_:pSubst.pTerm with 
   [psubst (x0:Variable)   (t0:pTerm)⇒t0]
   =false)).
∀( p : (t_size (val_to_term (abstr x t1))≤S m)).
∀( k : pTerm).

 (t_size k
  =t_size t1
   +free_occ_t
    match s in pSubst return λ_:pSubst.Variable with 
    [psubst (x0:Variable)   (t0:pTerm)⇒x0] t1
    *(t_size
      match s in pSubst return λ_:pSubst.pTerm with 
      [psubst (x0:Variable)   (t0:pTerm)⇒t0]
      -1)
  ∧(∀z0:Variable
    .free_occ_t z0 k
     =if veqb
           match s in pSubst return λ_:pSubst.Variable with 
           [psubst (y:Variable)   (t':pTerm)⇒y] z0 
      then free_occ_t z0 t1
               *free_occ_t z0
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t'] 
      else free_occ_t
               match s in pSubst return λ_:pSubst.Variable with 
               [psubst (y:Variable)   (t':pTerm)⇒y] t1
               *free_occ_t z0
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t']
               +free_occ_t z0 t1 )
  →t_size (val_to_term (abstr x k))
   =t_size (val_to_term (abstr x t1))
    +free_occ_v
     match s in pSubst return λ_:pSubst.Variable with 
     [psubst (x0:Variable)   (t0:pTerm)⇒x0] (abstr x t1)
     *(t_size
       match s in pSubst return λ_:pSubst.pTerm with 
       [psubst (x0:Variable)   (t0:pTerm)⇒t0]
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 (val_to_term (abstr x k))
      =if veqb
            match s in pSubst return λ_:pSubst.Variable with 
            [psubst (y:Variable)   (t':pTerm)⇒y] z0 
       then free_occ_v z0 (abstr x t1)
                *free_occ_t z0
                 match s in pSubst return λ_:pSubst.pTerm with 
                 [psubst (y:Variable)   (t':pTerm)⇒t'] 
       else free_occ_v
                match s in pSubst return λ_:pSubst.Variable with 
                [psubst (y:Variable)   (t':pTerm)⇒y] (abstr x t1)
                *free_occ_t z0
                 match s in pSubst return λ_:pSubst.pTerm with 
                 [psubst (y:Variable)   (t':pTerm)⇒t']
                +free_occ_v z0 (abstr x t1) )).

#n #s #m #t #v #x #t1 #H #HH #p #k

lapply HH lapply H elim s #y #t'
  whd in match (match psubst y t' in pSubst return λ_:pSubst.Variable with 
    [psubst (x0:Variable)   (t0:pTerm)⇒x0]) in ⊢ %;

  whd in match (match psubst y t' in pSubst return λ_:pSubst.pTerm with 
    [psubst (x0:Variable)   (t0:pTerm)⇒t0]) in ⊢ %;
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
∀( s : pSubst).
∀( m : ℕ).
∀( t : pTerm).
∀( t' : pTerm).
∀( u : pTerm).
∀( p : (t_size (appl t' u)≤S m)).
∀( k : pTerm).
∀( j : pTerm ).

 (t_size j
  =t_size u
   +free_occ_t
    match s in pSubst return λ_:pSubst.Variable with 
    [psubst (x:Variable)   (t0:pTerm)⇒x] u
    *(t_size
      match s in pSubst return λ_:pSubst.pTerm with 
      [psubst (x:Variable)   (t0:pTerm)⇒t0]
      -1)
  ∧(∀z0:Variable
    .free_occ_t z0 j
     =if veqb
           match s in pSubst return λ_:pSubst.Variable with 
           [psubst (y:Variable)   (t':pTerm)⇒y] z0 
      then free_occ_t z0 u
               *free_occ_t z0
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t'] 
      else free_occ_t
               match s in pSubst return λ_:pSubst.Variable with 
               [psubst (y:Variable)   (t':pTerm)⇒y] u
               *free_occ_t z0
                match s in pSubst return λ_:pSubst.pTerm with 
                [psubst (y:Variable)   (t':pTerm)⇒t']
               +free_occ_t z0 u )
  →t_size k
   =t_size t'
    +free_occ_t
     match s in pSubst return λ_:pSubst.Variable with 
     [psubst (x:Variable)   (t0:pTerm)⇒x] t'
     *(t_size
       match s in pSubst return λ_:pSubst.pTerm with 
       [psubst (x:Variable)   (t0:pTerm)⇒t0]
       -1)
   ∧(∀z0:Variable
     .free_occ_t z0 k
      =if veqb
            match s in pSubst return λ_:pSubst.Variable with 
            [psubst (y:Variable)   (t':pTerm)⇒y] z0 
       then free_occ_t z0 t'
                *free_occ_t z0
                 match s in pSubst return λ_:pSubst.pTerm with 
                 [psubst (y:Variable)   (t':pTerm)⇒t'] 
       else free_occ_t
                match s in pSubst return λ_:pSubst.Variable with 
                [psubst (y:Variable)   (t':pTerm)⇒y] t'
                *free_occ_t z0
                 match s in pSubst return λ_:pSubst.pTerm with 
                 [psubst (y:Variable)   (t':pTerm)⇒t']
                +free_occ_t z0 t' )
   →t_size (appl k j)
    =t_size (appl t' u)
     +free_occ_t
      match s in pSubst return λ_:pSubst.Variable with 
      [psubst (x:Variable)   (t0:pTerm)⇒x] (appl t' u)
      *(t_size
        match s in pSubst return λ_:pSubst.pTerm with 
        [psubst (x:Variable)   (t0:pTerm)⇒t0]
        -1)
    ∧(∀z0:Variable
      .free_occ_t z0 (appl k j)
       =if veqb
             match s in pSubst return λ_:pSubst.Variable with 
             [psubst (y:Variable)   (t':pTerm)⇒y] z0 
        then free_occ_t z0 (appl t' u)
                 *free_occ_t z0
                  match s in pSubst return λ_:pSubst.pTerm with 
                  [psubst (y:Variable)   (t':pTerm)⇒t'] 
        else free_occ_t
                 match s in pSubst return λ_:pSubst.Variable with 
                 [psubst (y:Variable)   (t':pTerm)⇒y] (appl t' u)
                 *free_occ_t z0
                  match s in pSubst return λ_:pSubst.pTerm with 
                  [psubst (y:Variable)   (t':pTerm)⇒t']
                 +free_occ_t z0 (appl t' u) )).

#n #s #m #t #t' #u #p #k #j

  elim s #y #t'
  whd in match (match psubst y t' in pSubst return λ_:pSubst.Variable with 
    [psubst (x0:Variable)   (t0:pTerm)⇒x0]) in ⊢ %;
  whd in match (match psubst y t' in pSubst return λ_:pSubst.pTerm with 
    [psubst (x0:Variable)   (t0:pTerm)⇒t0]) in ⊢ %;
  * #Hj_size #Hfoj * #Hk_size #Hfok %
  [ normalize >Hk_size >Hj_size normalize @eq_f
   cases (t_size t') // #n normalize /2/ 
  | #z normalize >(Hfoj z) >(Hfok z) normalize
    cut (veqb y z= true ∨ veqb y z= false) // * #Hyz >Hyz normalize /2/
  ]
qed.


let rec p_subst_sig (n: nat) s: Πt. (t_size t ≤ n) →
 Σu: pTerm. ((t_size u = (t_size t)+ (free_occ_t (match s with [psubst x t ⇒ x]) t) * ((t_size (match s with [psubst x t ⇒ t])) - 1)) ∧
  (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
   [ true ⇒ (free_occ_t z t) * (free_occ_t z match s with [psubst y t' ⇒ t'])
   | false ⇒ (free_occ_t (match s with [psubst y t' ⇒ y]) t) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_t z t)
   ])) ≝

 match n return λn. Πt. (t_size t ≤ n) → Σu: pTerm. ((t_size u = (t_size t)+ (free_occ_t (match s with [psubst x t ⇒ x]) t) * ((t_size (match s with [psubst x t ⇒ t])) - 1)) ∧
  (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
   [ true ⇒ (free_occ_t z t) * (free_occ_t z match s with [psubst y t' ⇒ t'])
   | false ⇒ (free_occ_t (match s with [psubst y t' ⇒ y]) t) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_t z t)
   ]))
  with
 [ O ⇒ λt.?
 | S m ⇒ λt. match t return λt.t_size t ≤ S m → Σu: pTerm. ((t_size u = (t_size t)+ (free_occ_t (match s with [psubst x t ⇒ x]) t) * ((t_size (match s with [psubst x t ⇒ t])) - 1)) ∧
   (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
   [ true ⇒ (free_occ_t z t) * (free_occ_t z match s with [psubst y t' ⇒ t'])
   | false ⇒ (free_occ_t (match s with [psubst y t' ⇒ y]) t) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_t z t)
   ]))
  with
   [ val_to_term v ⇒ match v return λv. t_size (val_to_term v) ≤ S m → Σu: pTerm. (t_size u = (t_size (val_to_term v))+ (free_occ_v (match s with [psubst x t ⇒ x]) v) * ((t_size (match s with [psubst x t ⇒ t])) - 1) ∧
     (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
      [ true ⇒ (free_occ_v z v) * (free_occ_t z match s with [psubst y t' ⇒ t'])
      | false ⇒ (free_occ_v (match s with [psubst y t' ⇒ y]) v) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_v z v)
      ]))
     with
    [ pvar x ⇒ match s return λs. t_size (val_to_term (pvar x)) ≤ S m → Σu: pTerm. (t_size u = (t_size (val_to_term (pvar x)))+ (free_occ_v (match s with [psubst x t ⇒ x]) (pvar x)) * ((t_size (match s with [psubst x t ⇒ t])) - 1) ∧
     (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
      [ true ⇒ (free_occ_v z (pvar x)) * (free_occ_t z match s with [psubst y t' ⇒ t'])
      | false ⇒ (free_occ_v (match s with [psubst y t' ⇒ y]) (pvar x)) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_v z (pvar x))
      ]))
       with
      [ psubst y t' ⇒ match veqb y x return λb. veqb y x = b → t_size (val_to_term (pvar x)) ≤ S m → Σu: pTerm. (t_size u = (t_size (val_to_term (pvar x)))+ (free_occ_v (match (psubst y t') with [psubst x t ⇒ x]) (pvar x)) * ((t_size (match (psubst y t') with [psubst x t ⇒ t])) - 1) ∧
       (∀z. free_occ_t z u = match veqb (match (psubst y t') with [psubst y t' ⇒ y]) z with
         [ true ⇒ (free_occ_v z (pvar x)) * (free_occ_t z match (psubst y t') with [psubst y t' ⇒ t'])
         | false ⇒ (free_occ_v (match (psubst y t') with [psubst y t' ⇒ y]) (pvar x)) * (free_occ_t z match (psubst y t') with [psubst y t' ⇒ t']) + (free_occ_v z (pvar x))
         ]))
       with
        [true ⇒λH.λp.mk_Sig … t' ? | false ⇒ λH.λp.mk_Sig … (val_to_term (pvar x)) ?] (refl …)
      ]
    | abstr x t1 ⇒ match veqb (match s with [psubst x t ⇒ x]) x return λb. veqb (match s with [psubst x t ⇒ x]) x = b → t_size (val_to_term (abstr x t1)) ≤ S m → Σu: pTerm. (t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_v match s with [psubst x t ⇒ x] (abstr x t1)) * ((t_size match s with [psubst x t ⇒ t]) - 1) ∧
       (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
         [ true ⇒ (free_occ_v z (abstr x t1)) * (free_occ_t z match s with [psubst y t' ⇒ t'])
         | false ⇒ (free_occ_v (match s with [psubst y t' ⇒ y]) (abstr x t1)) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_v z (abstr x t1))
         ]))
      with
       [ true ⇒ λH.λp. mk_Sig …  (val_to_term (abstr x t1)) ?
       | false ⇒ λH. match fvb_t x (match s with [psubst x t ⇒ t]) return λb. fvb_t x (match s with [psubst x t ⇒ t])=b → t_size (val_to_term (abstr x t1)) ≤ S m → Σu: pTerm. (t_size u = (t_size (val_to_term (abstr x t1)))+ (free_occ_v match s with [psubst x t ⇒ x] (abstr x t1)) * ((t_size match s with [psubst x t ⇒ t]) - 1) ∧
         (∀z. free_occ_t z u = match veqb (match s with [psubst y t' ⇒ y]) z with
           [ true ⇒ (free_occ_v z (abstr x t1)) * (free_occ_t z match s with [psubst y t' ⇒ t'])
           | false ⇒ (free_occ_v (match s with [psubst y t' ⇒ y]) (abstr x t1)) * (free_occ_t z match s with [psubst y t' ⇒ t']) + (free_occ_v z (abstr x t1))
           ]))
        with
         [ true ⇒ λHH. λp. let z ≝ (max (S match s with [psubst x t ⇒ match x with [variable n ⇒ n]]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t1) (fresh_var_t match s with [psubst x t ⇒ t]))))
                  in match (p_subst_sig m (psubst x (val_to_term (pvar ν(z)))) t1 ?) with
           [ mk_Sig a h ⇒ mk_Sig …  (val_to_term (abstr (ν(z)) (pi1 … (p_subst_sig m s a ?)))) ?]
         | false ⇒ λHH. λp. mk_Sig … (val_to_term (abstr x (pi1 … (p_subst_sig m s t1 ?)))) ?
         ] (refl …)
       ] (refl …)
    ]
   | appl t' u ⇒  λp. mk_Sig … (appl (pi1 …(p_subst_sig m s t' ? )) (pi1 … (p_subst_sig m s u ?))) ?
   ]
 ]
.
[ @(subst_aux_1 …)
| @(subst_aux_2 … m H p)
| @(subst_aux_3 … m H p)
| @(subst_aux_4 … m H p)
| @(subst_aux_5 … h p)
| @sigma_prop_gen #k #k_def #k_size @(p_subst_aux_6 n s m t v x t1 H HH p ? ? a h k k_size) //
| 7,8: @(subst_aux_7 … p)
| @sigma_prop_gen #k #_ @(subst_aux_8 n s m t v x ? H HH p)
| @(subst_aux_9 … p)
| @(subst_aux_10 t' u m p)
| @sigma_prop_gen #k #_
  @sigma_prop_gen #j #_ @(subst_aux_11 n s m t t' u p k j)
]
qed.

definition p_subst ≝ λt.λs. pi1 … (p_subst_sig (t_size t) s t ?).// qed.
definition p_subst_v ≝ λv.λs. pi1 … (p_subst_sig (t_size (val_to_term v)) s (val_to_term v) ?).// qed.

lemma atomic_subst: ∀x, t. (p_subst (val_to_term (pvar x)) (psubst x t)) = t.
#x #t change with (pi1 … (p_subst_sig …)) in match (p_subst (val_to_term (pvar x)) (psubst x t));
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match (t_size (val_to_term (pvar x)) );
normalize in match (p_subst_sig 1 (psubst x t) (val_to_term (pvar x)));
cut (∀gg.∀ tt. (pi1 pTerm
  (λu:pTerm
   .t_size u=1+(free_occ_t x (val_to_term (pvar x)))*((t_size t)-1)
    ∧(∀z:Variable
      .free_occ_t z u
       =if veqb x z 
        then (free_occ_t z (val_to_term (pvar x)))*(free_occ_t z t) 
        else (free_occ_t x (val_to_term (pvar x)))*(free_occ_t z t)
                 +free_occ_t z (val_to_term (pvar x))))
 (match veqb x x
 return λb. veqb x x = b → 1 ≤ 1 →
    Σu: pTerm. ?
    with
     [ true ⇒ λH: veqb x x = true.
        λp: 1 ≤ 1.
         «t, gg H p»
     | false ⇒ λH: veqb x x = false.
        λp: 1 ≤ 1.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb x x )) (le_n 1))) = t)
     [ 2: #gg >(gg …) //]
  #gg #tt >(veqb_true …) in gg tt ⊢ %;
  normalize // qed.

lemma no_subst: ∀x, y, t. veqb y x =false → p_subst (val_to_term (pvar x)) (psubst y t) =val_to_term (pvar x).
#x #y #t #H
change with (pi1 … (p_subst_sig …)) in match (p_subst (val_to_term (pvar x)) (psubst y t));
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match (t_size (val_to_term (pvar x)) );
whd in match (p_subst_sig 1 (psubst y t) (val_to_term (pvar x)) (le_n 1));
cut (∀gg.∀ tt. eq pTerm (pi1 pTerm
  (λu:pTerm
   .t_size u=(1+free_occ_t y (val_to_term (pvar x))*(t_size t-1))
    ∧(∀z:Variable
      .free_occ_t z u
       =if veqb y z 
        then (free_occ_t z (val_to_term (pvar x)))*(free_occ_t z t) 
        else (free_occ_t y (val_to_term (pvar x)))*(free_occ_t z t)
                 +(free_occ_t z (val_to_term (pvar x))) ))
 (match veqb y x
 return λb. veqb y x = b → 1 ≤ 1 →
    Σu: pTerm. ?
    with
     [ true ⇒ λH: veqb y x = true.
        λp: 1 ≤ 1.
         «t, gg H p»
     | false ⇒ λH: veqb y x = false.
        λp: 1 ≤ 1.
         «val_to_term (pvar x), tt H p»
     ] (refl bool (veqb y x )) (le_n 1)))  (val_to_term (pvar x)))
[2: #UU @(UU …)] #gg #tt >H in gg tt ⊢ %; #gg' #tt' normalize // qed.

lemma no_subst2: ∀x, t, u. p_subst (val_to_term (abstr x t)) (psubst x u) = (val_to_term (abstr x t)).
#x #t #u
change with (pi1 … (p_subst_sig …)) in match (p_subst (val_to_term (abstr x t)) (psubst x u));
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match ((t_size (val_to_term (abstr x t))));
cut (∀K, K1, K2. pi1 pTerm (λu0:pTerm
   .t_size u0=S (t_size t)+free_occ_t x (val_to_term (abstr x t))*(t_size u-1)
    ∧(∀z:Variable
      .free_occ_t z u0
       =if veqb x z 
        then free_occ_t z (val_to_term (abstr x t))*free_occ_t z u 
        else free_occ_t x (val_to_term (abstr x t))*free_occ_t z u
                 +free_occ_t z (val_to_term (abstr x t)) ))
 (match veqb x x return λb. veqb x x = b → S (t_size t) ≤ S (t_size t) →
    Σu: pTerm. ?
 with
  [ true ⇒ λH: veqb x x =true.
     λp: S (t_size t ) ≤ S (t_size t).
       «val_to_term (abstr x t), K H p »
  |  false  ⇒ λH: veqb x x =false. match fvb_t x u return λb'. fvb_t x u = b' →
                                       S (t_size t) ≤ S (t_size t) →
                                        Σu: pTerm. ?
              with
              [ true ⇒ λHH: fvb_t x u = true. λp:S (t_size t) ≤ S (t_size t). let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t) (fresh_var_t u))))
                  in match (p_subst_sig (t_size t) (psubst x (val_to_term (pvar ν(z)))) t (le_n ?)) with
                     [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (p_subst_sig (t_size t) (psubst x u) a (subst_aux_5 … h p))))), K1 H HH p a h»]
              | false ⇒ λHH: fvb_t x u = false. λp:S (t_size t) ≤ S (t_size t). «(val_to_term (abstr x (pi1 … (p_subst_sig (t_size t) (psubst x u) t (le_n ?))))), K2 H HH p »
              ] (refl bool (fvb_t x u))

  ] (refl bool (veqb x x))  (le_n (S (t_size t))))= val_to_term (abstr x t))
   [ 2: #K @K | #K #K1 #K2 >veqb_true in K K1 K2 ⊢ %; normalize #K #K1 #K2 //]
qed.
(*
axiom daemon: False.
*)


axiom abstr_step_subst: ∀x, y, t, u. fvb_t x u = false →
  veqb y x = false →
   p_subst (val_to_term (abstr x t)) (psubst y u) = (val_to_term (abstr x (p_subst t (psubst y u)))).


(*
lemma abstr_step_subst: ∀x, y, t, u.
 fvb_t x u = false →
  veqb y x = false →
   p_subst (val_to_term (abstr x t)) (psubst y u) = (val_to_term (abstr x (p_subst t (psubst y u)))).
#x #y #t #u #fv #veq whd in match (p_subst ? ?);
whd in match (match ? in pSubst with [_ ⇒ ?]);
whd in match (match ? in pSubst with [_ ⇒ ?]);

cut (∀K, K1, K2. pi1 pTerm
  (λu0:pTerm
   .t_size u0
    =plus (t_size (val_to_term (abstr x t)))
     (free_occ_t y (val_to_term (abstr x t))*(minus (t_size u) 1))
    ∧(∀z:Variable
      .free_occ_t z u0
       =if veqb y z 
        then free_occ_t z (val_to_term (abstr x t))*free_occ_t z u 
        else plus (free_occ_t y (val_to_term (abstr x t))*free_occ_t z u)
                 (free_occ_t z (val_to_term (abstr x t)))))
 (match veqb y x
return λb.
veqb y x = b
→ S (t_size t) ≤ S (t_size t)
→ Σu: pTerm. 
 ?
with
  [ true ⇒ 
   λH: veqb y x =true.
     λp: S (t_size t ) ≤ S (t_size t).
       «val_to_term (abstr x t), K H p »
  | false ⇒
   λH: veqb y x =false. match fvb_t x u
       return λb'.
         fvb_t x u = b'
         → S (t_size t) ≤ S (t_size t)
         → Σu: pTerm. ?
       with
        [ true ⇒
          λHH: fvb_t x u = true. λp:S (t_size t) ≤ S (t_size t).
           let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t) (fresh_var_t u))))
           in
            match (p_subst_sig (t_size t) (psubst x (val_to_term (pvar (variable z)))) t (le_n ?))
            with
             [ mk_Sig a h ⇒ «(val_to_term (abstr (variable z) (pi1 … (p_subst_sig (t_size t) (psubst y u) a (subst_aux_5 … h p))))), K1 H HH p a h»]
        | false ⇒
         λHH: fvb_t x u = false. λp:S (t_size t) ≤ S (t_size t).
          «(val_to_term (abstr x (pi1 … (p_subst_sig (t_size t) (psubst y u) t (le_n ?))))), K2 H HH p »]
      (refl bool (fvb_t x u))
  ] (refl bool (veqb y x))  (le_n (S (t_size t))))= val_to_term (abstr x (p_subst t (psubst y u)))
)
[ >veq >fv #K #K1 #K2  // | #K @K                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         whd in match (t_size (val_to_term (abstr x t))); normalize
@K

 match veqb y x return λb. veqb y x = b → S (t_size t) ≤ S (t_size t) →
    Σu: pTerm. ?
 with
  [ true ⇒ 
   λH: veqb y x =true.
     λp: S (t_size t ) ≤ S (t_size t).
       «val_to_term (abstr x t), K H p »
  | false ⇒ 
   λH: veqb y x =false. match fvb_t x u 
       return λb'.
         fvb_t x u = b'
         → S (t_size t) ≤ S (t_size t) 
         → Σu: pTerm. ?
       with
        [ true ⇒
          λHH: fvb_t x u = true. λp:S (t_size t) ≤ S (t_size t).
           let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t) (fresh_var_t u))))
           in
            match (p_subst_sig (t_size t) (psubst x (val_to_term (pvar ν(z)))) t (le_n ?))
            with
             [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (p_subst_sig (t_size t) (psubst y u) a (subst_aux_5 … h p))))), K1 H HH p a h»]
        | false ⇒
         λHH: fvb_t x u = false. λp:S (t_size t) ≤ S (t_size t).
          «(val_to_term (abstr x (pi1 … (p_subst_sig (t_size t) (psubst y u) t (le_n ?))))), K2 H HH p »
              ] (refl bool (fvb_t x u))
  ] (refl bool (veqb y x))  (le_n (S (t_size t))))= val_to_term (abstr x (p_subst t (psubst y u))))
[ >veq >fv normalize #K #K1 #K2 // | #K 
 whd in match (p_subst_sig ? ? ? ?);
 whd in match (match ? in pSubst with [_ ⇒ ?]); 
 whd in match (t_size (val_to_term (abstr x t))); 
 whd in match (match ? in pSubst with [_ ⇒ ?]);
 whd in match (match ? in pSubst with [_ ⇒ ?]); 
 whd in match (match ? in pSubst with [_ ⇒ ?]);
 whd in match (match ? in pSubst with [_ ⇒ ?]);
 @K






whd in match (t_size (val_to_term (abstr x t)));

cut (∀K, K2. (pi1 pTerm
  (λu0:pTerm
   .And (t_size u0
    =(plus (t_size (val_to_term (abstr x t)))
     ((free_occ_t y (val_to_term (abstr x t)))*(minus (t_size u) 1 ))) )
     (∀zz:Variable
      .free_occ_t zz u0
       =if veqb y zz 
        then free_occ_t zz (val_to_term (abstr x t))*free_occ_t zz u 
        else plus (free_occ_t y (val_to_term (abstr x t))*free_occ_t zz u)
                  (free_occ_t zz (val_to_term (abstr x t)) )))
  ((match fvb_t x u 
    with [ true ⇒ (λHH:fvb_t x u=true
              .λp:t_size (val_to_term (abstr x t))≤S (t_size t)
               .(let (z:ℕ) ≝
                        max
                        (S
                         match y in Variable return λ_:Variable.ℕ with 
                         [variable (n0:ℕ)⇒n0])
                        (max
                         (S
                          match x in Variable return λ_:Variable.ℕ with 
                          [variable (nx:ℕ)⇒nx])
                         (max (fresh_var_t t) (fresh_var_t u))) in 
                 match 
                 p_subst_sig (t_size t) (psubst x (val_to_term (pvar (variable z)))) t
                 (subst_aux_7 x t (t_size t) p)
                  in Sig
                  return 
                 λ_:(Σu0:pTerm
                        .t_size u0
                         =t_size t+free_occ_t x t*(t_size (val_to_term (pvar (variable z)))-1)
                         ∧(∀z0:Variable
                           .free_occ_t z0 u0
                            =if veqb x z0 
                             then free_occ_t z0 t*free_occ_t z0 (val_to_term (pvar (variable z))) 
                             else free_occ_t x t*free_occ_t z0 (val_to_term (pvar (variable z)))
                                      +free_occ_t z0 t ))
                 .(Σu0:pTerm
                   .t_size u0
                    =t_size (val_to_term (abstr x t))
                     +free_occ_v y (abstr x t)*(t_size u-1)
                    ∧(∀z0:Variable
                      .free_occ_t z0 u0
                       =if veqb y z0 
                        then free_occ_v z0 (abstr x t)*free_occ_t z0 u 
                        else free_occ_v y (abstr x t)*free_occ_t z0 u
                                 +free_occ_v z0 (abstr x t) ))
                  with 
                 [mk_Sig
                  (a:pTerm)
                   
                  (h:
                  (t_size a
                   =t_size t+free_occ_t x t*(t_size (val_to_term (pvar (variable z)))-1)
                   ∧(∀z0:Variable
                     .free_occ_t z0 a
                      =if veqb x z0 
                       then free_occ_t z0 t*free_occ_t z0 (val_to_term (pvar (variable z))) 
                       else free_occ_t x t*free_occ_t z0 (val_to_term (pvar (variable z)))
                                +free_occ_t z0 t )))⇒
                  «val_to_term
                   (abstr (variable z)
                    (pi1 pTerm
                     (λu0:pTerm
                      .t_size u0=t_size a+free_occ_t y a*(t_size u-1)
                       ∧(∀z0:Variable
                         .free_occ_t z0 u0
                          =if veqb y z0 
                           then free_occ_t z0 a*free_occ_t z0 u 
                           else free_occ_t y a*free_occ_t z0 u+free_occ_t z0 a ))
                     (p_subst_sig (t_size t) (psubst y u) a
                      (subst_aux_5 t x z a (t_size t) h p)))),
                  K HH p»])) 
    | false ⇒ (λHH:fvb_t x u=false 
              .λp:t_size (val_to_term (abstr x t))≤S (t_size t)
               .«val_to_term
                 (abstr x
                  (pi1 pTerm
                   (λu0:pTerm
                    .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                     ∧(∀zzz:Variable
                       .free_occ_t zzz u0
                        =if veqb y zzz 
                         then free_occ_t zzz t*free_occ_t zzz u 
                         else free_occ_t y t*free_occ_t zzz u+free_occ_t zzz t ))
                   (p_subst_sig (t_size t) (psubst y u) t
                    (subst_aux_7 x t (t_size t) p)))),
                K2 HH p») ])
   (refl bool (fvb_t x u)) (le_n (t_size (val_to_term (abstr x t)))))
  =val_to_term (abstr x (p_subst t (psubst y u))))))

cut (∀K, K1, K2. pi1 pTerm
  (λu0:pTerm
   .t_size u0
    =t_size (val_to_term (abstr x t))
     +free_occ_t y (val_to_term (abstr x t))*(t_size u-1)
    ∧(∀z:Variable
      .free_occ_t z u0
       =if veqb y z 
        then free_occ_t z (val_to_term (abstr x t))*free_occ_t z u 
        else free_occ_t y (val_to_term (abstr x t))*free_occ_t z u
                 +free_occ_t z (val_to_term (abstr x t)) ))
 (match veqb y x return λb. veqb y x = b → S (t_size t) ≤ S (t_size t) →
    Σu: pTerm. ?
 with
  [ true ⇒ λH: veqb y x =true.
     λp: S (t_size t ) ≤ S (t_size t).
       «val_to_term (abstr x t), K H p »
  |  false  ⇒ λH: veqb y x =false. match fvb_t x u return λb'. fvb_t x u = b' →
                                       S (t_size t) ≤ S (t_size t) →
                                        Σu: pTerm. ?
              with
              [ true ⇒ λHH: fvb_t x u = true. λp:S (t_size t) ≤ S (t_size t). let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t) (fresh_var_t u))))
                  in match (p_subst_sig (t_size t) (psubst x (val_to_term (pvar ν(z)))) t (le_n ?)) with
                     [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (p_subst_sig (t_size t) (psubst y u) a (subst_aux_5 … h p))))), K1 H HH p a h»]
              | false ⇒ λHH: fvb_t x u = false. λp:S (t_size t) ≤ S (t_size t). «(val_to_term (abstr x (pi1 … (p_subst_sig (t_size t) (psubst y u) t (le_n ?))))), K2 H HH p »
              ] (refl bool (fvb_t x u))
  ] (refl bool (veqb y x))  (le_n (S (t_size t))))= val_to_term (abstr x (p_subst t (psubst y u))))
[ 2: whd in match (match ? in pSubst with [_ ⇒ ?]);
     whd in match (match ? in pSubst with [_ ⇒ ?]);
     whd in match (match ? in pSubst with [_ ⇒ ?]);
     whd in match (match ? in pSubst with [_ ⇒ ?]);
     whd in match (match ? in pSubst with [_ ⇒ ?]); #K lapply (K ? ?) 
  [ #_ >fv #abs destruct | >veq #abs destruct
  | #K1 lapply (K1 ?) [ #_ #_ #eq %
   [ whd in match (t_size ?); whd in match (pi1 … ?);
  @K

cut (∀K, K1, K2. pi1 pTerm
  (λu0:pTerm
   .t_size u0=S (t_size t)+free_occ_t y (val_to_term (abstr x t))*(t_size u-1)
    ∧(∀z:Variable
      .free_occ_t z u0
       =if veqb y z 
        then free_occ_t z (val_to_term (abstr x t))*free_occ_t z u 
        else free_occ_t y (val_to_term (abstr x t))*free_occ_t z u
                 +free_occ_t z (val_to_term (abstr x t)) ))
  (match veqb y x return λb. veqb y x = b → S (t_size t) ≤ S (t_size t) →
    Σu: pTerm. ?
 with
  [ true ⇒ λH: veqb y x =true.
     λp: S (t_size t ) ≤ S (t_size t).
       «val_to_term (abstr x t), K H p »
  |  false  ⇒ λH: veqb y x =false. match fvb_t x u return λb'. fvb_t x u = b' →
                                       S (t_size t) ≤ S (t_size t) →
                                        Σu: pTerm. ?
              with
              [ true ⇒ λHH: fvb_t x u = true. λp:S (t_size t) ≤ S (t_size t). let z ≝ (max (S match x with [variable n ⇒ n]) (max (S match x with [variable nx⇒ nx]) (max (fresh_var_t t) (fresh_var_t u))))
                  in match (p_subst_sig (t_size t) (psubst x (val_to_term (pvar ν(z)))) t (le_n ?)) with
                     [ mk_Sig a h ⇒ «(val_to_term (abstr (ν(z)) (pi1 … (p_subst_sig (t_size t) (psubst y u) a (subst_aux_5 … h p))))), K1 H HH p a h»]
              | false ⇒ λHH: fvb_t x u = false. λp:S (t_size t) ≤ S (t_size t). «(val_to_term (abstr x (pi1 … (p_subst_sig (t_size t) (psubst y u) t (le_n ?))))), K2 H HH p »
              ] (refl bool (fvb_t x u))

  ] (refl bool (veqb y x))  (le_n (S (t_size t))))
  =val_to_term (abstr x (p_subst t (psubst y u))))
  [ 2: #K @K


whd in match (p_subst_sig ? ? ? ?);
whd in match (match psubst y u in pSubst return λ_:pSubst.Variable with 
         [psubst (x0:Variable)   (t0:pTerm)⇒x0]);


lapply (eq_ind_r bool false (λveqbyx. λH10.( pi1 pTerm
  (λu0:pTerm.
  (t_size u0 =(t_size (val_to_term (abstr x t))) + (free_occ_t y (val_to_term (abstr x t)))*(t_size u-1))
    ∧(∀zz:Variable
      .(free_occ_t zz u0)
       =if (veqb y zz)
        then (free_occ_t zz (val_to_term (abstr x t)))*(free_occ_t zz u)
        else (free_occ_t y (val_to_term (abstr x t)))*(free_occ_t zz u)
                 +(free_occ_t zz (val_to_term (abstr x t)))))
  ((match (veqbyx) return λveqbyx2.∀H5:veqbyx = veqbyx2. ? 
    with [ true ⇒ (λH5:veqbyx=true
              .λp:t_size (val_to_term (abstr x t))≤S (t_size t)
               .«val_to_term (abstr x t),
                (*subst_aux_4 t x (psubst y u) (t_size t) H5 p*) ?») 
    | false ⇒ (λH5:veqbyx=false
              .(match fvb_t x
                     match psubst y u in pSubst return λH0:pSubst.pTerm with 
                     [psubst (x0:Variable)   (t0:pTerm)⇒t0] return λAAAA. ∀BBBB:fvb_t x
                     match psubst y u in pSubst return λH0:pSubst.pTerm with 
                     [psubst (x0:Variable)   (t0:pTerm)⇒t0] =AAAA. ?
                with [true ⇒ (λHH:fvb_t x
                                  match psubst y u in pSubst return λ_:pSubst.pTerm with 
                                  [psubst (x0:Variable)   (t0:pTerm)⇒t0]
                                  =true
                          .λp:t_size (val_to_term (abstr x t))≤S (t_size t)
                           .(let (z:ℕ) ≝
                                    max
                                    (S
                                     match psubst y u in pSubst return λ_:pSubst.ℕ with 
                                     [psubst (x0:Variable)   (t0:pTerm)⇒
                                      match x0 in Variable return λ_:Variable.ℕ with 
                                      [variable (n0:ℕ)⇒n0]])
                                    (max
                                     (S
                                      match x in Variable return λ_:Variable.ℕ with 
                                      [variable (nx:ℕ)⇒nx])
                                     (max (fresh_var_t t)
                                      (fresh_var_t
                                       match psubst y u in pSubst return λ_:pSubst.pTerm
                                        with 
                                       [psubst (x0:Variable)   (t0:pTerm)⇒t0]))) in 
                             match 
                             p_subst_sig (t_size t) (psubst x (val_to_term (pvar (variable z)))) t
                             (subst_aux_7 x t (t_size t) p)
                              in Sig
                              return 
                             λ_:(Σu0:pTerm
                                    .t_size u0
                                     =t_size t
                                      +free_occ_t
                                       match psubst x (val_to_term (pvar (variable z)))
                                        in pSubst
                                        return λ_:pSubst.Variable
                                        with 
                                       [psubst (x0:Variable)   (t0:pTerm)⇒x0] t
                                       *(t_size
                                         match psubst x (val_to_term (pvar (variable z)))
                                          in pSubst
                                          return λ_:pSubst.pTerm
                                          with 
                                         [psubst (x0:Variable)   (t0:pTerm)⇒t0]
                                         -1)
                                     ∧(∀z0:Variable
                                       .free_occ_t z0 u0
                                        =if veqb 
                                              match psubst x (val_to_term (pvar (variable z)))
                                               in pSubst
                                               return λ_:pSubst.Variable
                                               with 
                                              [psubst (y0:Variable)   (t':pTerm)⇒y0] z0 
                                        then free_occ_t z0 t
                                                  *free_occ_t z0
                                                   match psubst x (val_to_term (pvar (variable z)))
                                                    in pSubst
                                                    return λ_:pSubst.pTerm
                                                    with 
                                                   [psubst (y0:Variable)   (t':pTerm)⇒t'] 
                                        else free_occ_t
                                                  match psubst x (val_to_term (pvar (variable z)))
                                                   in pSubst
                                                   return λ_:pSubst.Variable
                                                   with 
                                                  [psubst (y0:Variable)   (t':pTerm)⇒y0] t
                                                  *free_occ_t z0
                                                   match psubst x (val_to_term (pvar (variable z)))
                                                    in pSubst
                                                   return λ_:pSubst.pTerm
                                                    with 
                                                   [psubst (y0:Variable)   (t':pTerm)⇒t']
                                                  +free_occ_t z0 t ))
                             .(Σu0:pTerm
                              .t_size u0
                                =t_size (val_to_term (abstr x t))
                                 +free_occ_v y (abstr x t)
                                  *(t_size
                                    (match psubst y u in pSubst  return λ_:pSubst.pTerm
                                   with 
                                    [psubst (x0:Variable)   (t0:pTerm)⇒t0])
                                   -1)
                               ∧(∀z0:Variable
                                  .free_occ_t z0 u0
                                   =if veqb y z0 
                                    then free_occ_v z0 (abstr x t)
                                             *free_occ_t z0
                                              match psubst y u
                                               in pSubst
                                               return λ_:pSubst.pTerm
                                               with 
                                              [psubst (y0:Variable)   (t':pTerm)⇒t'] 
                                    else free_occ_v y (abstr x t)
                                             *free_occ_t z0
                                              match psubst y u
                                               in pSubst
                                               return λ_:pSubst.pTerm
                                               with 
                                              [psubst (y0:Variable)   (t':pTerm)⇒t']
                                             +free_occ_v z0 (abstr x t) ))
                              with
                            [mk_Sig
                              (a:pTerm)
                               
                              (h:
                              (t_size a
                               =t_size t
                                +free_occ_t
                                 match psubst x (val_to_term (pvar (variable z)))
                                  in pSubst
                                  return λ_:pSubst.Variable
                                  with 
                                 [psubst (x0:Variable)   (t0:pTerm)⇒x0] t
                                 *(t_size
                                   match psubst x (val_to_term (pvar (variable z)))
                                    in pSubst
                                    return λ_:pSubst.pTerm
                                    with 
                                   [psubst (x0:Variable)   (t0:pTerm)⇒t0]
                                   -1)
                               ∧(∀z0:Variable
                                 .free_occ_t z0 a
                                  =if veqb
                                        match psubst x (val_to_term (pvar (variable z)))
                                         in pSubst
                                         return λ_:pSubst.Variable
                                         with 
                                        [psubst (y0:Variable)   (t':pTerm)⇒y0] z0 
                                   then free_occ_t z0 t
                                            *free_occ_t z0
                                             match psubst x (val_to_term (pvar (variable z)))
                                              in pSubst
                                              return λ_:pSubst.pTerm
                                              with 
                                             [psubst (y0:Variable)   (t':pTerm)⇒t'] 
                                   else free_occ_t
                                            match psubst x (val_to_term (pvar (variable z)))
                                             in pSubst
                                             return λ_:pSubst.Variable
                                             with 
                                            [psubst (y0:Variable)   (t':pTerm)⇒y0] t
                                            *free_occ_t z0
                                             match psubst x (val_to_term (pvar (variable z)))
                                              in pSubst
                                              return λ_:pSubst.pTerm
                                              with 
                                             [psubst (y0:Variable)   (t':pTerm)⇒t']
                                            +free_occ_t z0 t )))⇒
                              «val_to_term
                               (abstr (variable z)
                                (pi1 pTerm
                                 (λu0:pTerm
                                  .t_size u0
                                   =t_size a
                                    +free_occ_t y a
                                     *(t_size
                                       match psubst y u in pSubst return λ_:pSubst.pTerm
                                        with 
                                       [psubst (x0:Variable)   (t0:pTerm)⇒t0]
                                       -1)
                                   ∧(∀z0:Variable
                                     .free_occ_t z0 u0
                                     =if veqb y z0 
                                       then free_occ_t z0 a
                                                *free_occ_t z0
                                                 match psubst y u
                                                  in pSubst
                                                  return λ_:pSubst.pTerm
                                                  with 
                                                 [psubst (y0:Variable)   (t':pTerm)⇒t'] 
                                       else free_occ_t y a
                                                *free_occ_t z0
                                                 match psubst y u
                                                  in pSubst
                                                  return λ_:pSubst.pTerm
                                                  with 
                                                 [psubst (y0:Variable)   (t':pTerm)⇒t']
                                                +free_occ_t z0 a ))
                                 (p_subst_sig (t_size t) (psubst y u) a
                                  (subst_aux_5 t x z a (t_size t) h p)))), ?»])) 
                | false ⇒ (λHH:fvb_t x
                                  match psubst y u in pSubst return λ_:pSubst.pTerm with 
                                  [psubst (x0:Variable)   (t0:pTerm)⇒t0]
                                  =false
                          . ?)] )
               (refl bool
                (fvb_t x
                 match psubst y u in pSubst return λ_:pSubst.pTerm with 
                 [psubst (x0:Variable)   (t0:pTerm)⇒t0])))] ) 
   (refl bool (veqbyx)) (le_n (t_size (val_to_term (abstr x t)))))
  =val_to_term (abstr x (p_subst t (psubst y u) ) ) ) ) ? (veqb y x) veq)
  
 [ 2: cases (?:False) lapply H5 >H10 #abs destruct
 | 3: lapply HH whd in match (match psubst y u in pSubst return λ_:pSubst.pTerm with 
   [psubst (x0:Variable)   (t0:pTerm)⇒t0]); -HH #HH cases (? : False) lapply HH >fv #abs destruct 
 | 4: #p % [ @(val_to_term
                             (abstr x
                              (pi1 pTerm
                               (λu0:pTerm
                                .t_size u0
                                 =t_size t
                                  +free_occ_t y t
                                   *(t_size
                                     match psubst y u in pSubst return λ_:pSubst.pTerm
                                      with 
                                     [psubst (x0:Variable)   (t0:pTerm)⇒t0]
                                     -1)
                                 ∧(∀zzz:Variable
                                   .(free_occ_t zzz u0)
                                    =if (veqb y zzz) 
                                     then (free_occ_t zzz t)
                                              *(free_occ_t zzz
                                               match psubst y u
                                                in pSubst
                                                return λ_:pSubst.pTerm
                                                with 
                                               [psubst (y0:Variable)   (t':pTerm)⇒t']) 
                                     else free_occ_t y t
                                              *(free_occ_t zzz
                                               match psubst y u
                                                in pSubst
                                                return λ_:pSubst.pTerm
                                                with 
                                               [psubst (y0:Variable)   (t':pTerm)⇒t'])
                                              +(free_occ_t zzz t) ))
                               (p_subst_sig (t_size t) (psubst y u) t
                                (subst_aux_7 x t (t_size t) p)))))
  | -HH whd in match (match psubst y u in pSubst return λ_:pSubst.pTerm with [psubst (x0:Variable)   (t0:pTerm)⇒t0]);
   @conj
   [ whd in match (t_size ?); inversion (p_subst_sig (t_size t) (psubst y u) t (subst_aux_7 x t (t_size t) p))
    whd in match (match psubst y u in pSubst return λH11:pSubst.Variable with [psubst (x0:Variable)   (t0:pTerm)⇒x0]);
    whd in match (match psubst y u in pSubst return λH12:pSubst.pTerm with [psubst (x0:Variable)   (t0:pTerm)⇒t0]);
    #term0 #H11 #eq lapply (proj1 … H11) #eq2 >eq2 normalize >veq whd in match (if false then O else free_occ_t y t ); //
   | #z inversion (p_subst_sig (t_size t) (psubst y u) t (subst_aux_7 x t (t_size t) p))
    whd in match (match psubst y u in pSubst return λH11:pSubst.Variable with [psubst (x0:Variable)   (t0:pTerm)⇒x0]);
    whd in match (match psubst y u in pSubst return λH12:pSubst.pTerm with [psubst (x0:Variable)   (t0:pTerm)⇒t0]);
    #term0 #H13 #eq inversion (veqb y z)
    [ #veqbyz whd in match (if true then free_occ_v z (abstr x t)*free_occ_t z u else free_occ_v y (abstr x t)*free_occ_t z u+free_occ_v z (abstr x t) );
     normalize cut (veqb z x = false)
     [ lapply (veqb_true_to_eq y z) * #veq_to_eq #_
      lapply (veq_to_eq veqbyz) #eq <eq @veq
     | #veqbzx >veqbzx whd in match (if false then O else free_occ_t z term0);
      whd in match (if false then O else free_occ_t z t); lapply (proj2 … H13) #freocc lapply (freocc z) >veqbyz
      whd in match (if true then free_occ_t z t*free_occ_t z u else free_occ_t y t*free_occ_t z u+free_occ_t z t);
      #th @th ]
    | #veqbyz whd in match (if false then free_occ_v z (abstr x t)*free_occ_t z u else free_occ_v y (abstr x t)*free_occ_t z u+free_occ_v z (abstr x t) );
      normalize inversion (veqb z x)
      [ #veqbzx whd in match (if true then O else free_occ_t z term0); >veq
        whd in match (if false then O else free_occ_t y t);
        lapply (veqb_fv z x u veqbzx) #eq2 lapply fv <eq2 #fvz lapply (free_occ_to_fv z …) #fotf
        lapply (proj1 … fotf) -fotf #fotf lapply (fotf u) * #_ #Hfin lapply (Hfin fvz) #focc
        >focc lapply (times_O (free_occ_t y t)) #Htimes >Htimes //
      | #veqbzx whd in match (if false then O else free_occ_t z term0); >veq
       whd in match (if false then O else free_occ_t y t);
       whd in match (if false then O else free_occ_t z t);
       lapply (proj2 … H13) -H13 #H13 lapply (H13 z) -H13 >veqbyz
       whd in match (if false then free_occ_t z t*free_occ_t z u else free_occ_t y t*free_occ_t z u+free_occ_t z t);
       #H @H
      ]
    ]
   ]
  ]  
  | 5: #H @H 
  | whd in match (match psubst y u in pSubst return λH30:pSubst.pTerm with [psubst (x0:Variable)   (t0:pTerm)⇒t0]); 
    whd in match (match psubst y u in pSubst return λH29:pSubst.ℕ with [psubst (x0:Variable)   (t0:pTerm)⇒ match x0 in Variable return λ_:Variable.ℕ with [variable (n0:ℕ)⇒n0]]);
    whd in match (match psubst x (val_to_term (pvar ?)) in pSubst return λH29:pSubst.Variable with [psubst (x0:Variable)   (t0:pTerm)⇒x0]);
    whd in match (match psubst x (val_to_term (pvar ?)) in pSubst return λH30:pSubst.pTerm with [psubst (x0:Variable)   (t0:pTerm)⇒t0]);
    whd in match (match psubst y u in pSubst return λH31:pSubst.Variable with [psubst (x0:Variable)   (t0:pTerm)⇒x0]);

    whd in ⊢ (? ? (? ? ? %) ?);
    check Sig_inv_ind
    check  ( (pi1 pTerm
  (λu0:pTerm
   .And (t_size u0
    =(plus (t_size (val_to_term (abstr x t)))
     ((free_occ_t y (val_to_term (abstr x t)))*(minus (t_size u) 1 ))) )
     (∀zz:Variable
      .free_occ_t zz u0
       =if veqb y zz 
        then free_occ_t zz (val_to_term (abstr x t))*free_occ_t zz u 
        else plus (free_occ_t y (val_to_term (abstr x t))*free_occ_t zz u)
                  (free_occ_t zz (val_to_term (abstr x t)) )))
  ((match fvb_t x u 
    with [ true ⇒ (λHH:fvb_t x u=true
              .λp:t_size (val_to_term (abstr x t))≤S (t_size t)
               .(let (z:ℕ) ≝
                        max
                        (S
                         match y in Variable return λ_:Variable.ℕ with 
                         [variable (n0:ℕ)⇒n0])
                        (max
                         (S
                          match x in Variable return λ_:Variable.ℕ with 
                          [variable (nx:ℕ)⇒nx])
                         (max (fresh_var_t t) (fresh_var_t u))) in 
                 match 
                 p_subst_sig (t_size t) (psubst x (val_to_term (pvar (variable z)))) t
                 (subst_aux_7 x t (t_size t) p)
                  in Sig
                  return 
                 λ_:(Σu0:pTerm
                        .t_size u0
                         =t_size t+free_occ_t x t*(t_size (val_to_term (pvar (variable z)))-1)
                         ∧(∀z0:Variable
                           .free_occ_t z0 u0
                            =if veqb x z0 
                             then free_occ_t z0 t*free_occ_t z0 (val_to_term (pvar (variable z))) 
                             else free_occ_t x t*free_occ_t z0 (val_to_term (pvar (variable z)))
                                      +free_occ_t z0 t ))
                 .(Σu0:pTerm
                   .t_size u0
                    =t_size (val_to_term (abstr x t))
                     +free_occ_v y (abstr x t)*(t_size u-1)
                    ∧(∀z0:Variable
                      .free_occ_t z0 u0
                       =if veqb y z0 
                        then free_occ_v z0 (abstr x t)*free_occ_t z0 u 
                        else free_occ_v y (abstr x t)*free_occ_t z0 u
                                 +free_occ_v z0 (abstr x t) ))
                  with 
                 [mk_Sig
                  (a:pTerm)
                   
                  (h:
                  (t_size a
                   =t_size t+free_occ_t x t*(t_size (val_to_term (pvar (variable z)))-1)
                   ∧(∀z0:Variable
                     .free_occ_t z0 a
                      =if veqb x z0 
                       then free_occ_t z0 t*free_occ_t z0 (val_to_term (pvar (variable z))) 
                       else free_occ_t x t*free_occ_t z0 (val_to_term (pvar (variable z)))
                                +free_occ_t z0 t )))⇒
                  «?(*val_to_term
                   (abstr (variable z)
                    (pi1 pTerm
                     (λu0:pTerm
                      .t_size u0=t_size a+free_occ_t y a*(t_size u-1)
                       ∧(∀z0:Variable
                         .free_occ_t z0 u0
                          =if veqb y z0 
                           then free_occ_t z0 a*free_occ_t z0 u 
                           else free_occ_t y a*free_occ_t z0 u+free_occ_t z0 a ))
                     (p_subst_sig (t_size t) (psubst y u) a
                      (subst_aux_5 t x z a (t_size t) h p))))*),
                  ?(*match 
                  (eq_ind_r bool false (λx0:bool.λ_:x0=false.x0=true→False)
                   (λabs:false=true
                    .eq_ind_r bool false (λx0:bool.λ_:x0=false.x0=false→False)
                     (λH50:false=false.bool_discr false true abs False) false
                     (refl bool false) (refl bool false))
                   (fvb_t x u) fv HH
                  :False)
                   in False
                   return 
                  λ_:False
                  .(t_size
                    (val_to_term
                     (abstr (variable z)
                      (pi1 pTerm
                       (λu0:pTerm
                        .t_size u0=t_size a+free_occ_t y a*(t_size u-1)
                         ∧(∀z0:Variable
                           .free_occ_t z0 u0
                            =if veqb y z0 
                             then free_occ_t z0 a*free_occ_t z0 u 
                             else free_occ_t y a*free_occ_t z0 u+free_occ_t z0 a ))
                       (p_subst_sig (t_size t) (psubst y u) a
                        (subst_aux_5 t x z a (t_size t) h p)))))
                    =t_size (val_to_term (abstr x t))
                     +free_occ_v y (abstr x t)*(t_size u-1)
                    ∧(∀z0:Variable
                      .free_occ_t z0
                       (val_to_term
                        (abstr (variable z)
                         (pi1 pTerm
                          (λu0:pTerm
                           .t_size u0=t_size a+free_occ_t y a*(t_size u-1)
                            ∧(∀z00:Variable
                              .free_occ_t z00 u0
                               =if veqb y z00 
                                then free_occ_t z00 a*free_occ_t z00 u 
                                else free_occ_t y a*free_occ_t z00 u
                                         +free_occ_t z00 a ))
                          (p_subst_sig (t_size t) (psubst y u) a
                           (subst_aux_5 t x z a (t_size t) h p)))))
                       =if veqb y z0 
                        then free_occ_v z0 (abstr x t)*free_occ_t z0 u 
                        else free_occ_v y (abstr x t)*free_occ_t z0 u
                                 +free_occ_v z0 (abstr x t) ))
                   with 
                  []*)»])) 
    | false ⇒ (λHH:fvb_t x u=false 
              .λp:t_size (val_to_term (abstr x t))≤S (t_size t)
               .«val_to_term
                 (abstr x
                  (pi1 pTerm
                   (λu0:pTerm
                    .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                     ∧(∀zzz:Variable
                       .free_occ_t zzz u0
                        =if veqb y zzz 
                         then free_occ_t zzz t*free_occ_t zzz u 
                         else free_occ_t y t*free_occ_t zzz u+free_occ_t zzz t ))
                   (p_subst_sig (t_size t) (psubst y u) t
                    (subst_aux_7 x t (t_size t) p)))),
                conj
                (t_size
                 (val_to_term
                  (abstr x
                   (pi1 pTerm
                    (λu0:pTerm
                     .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                      ∧(∀zzz:Variable
                        .free_occ_t zzz u0
                         =if veqb y zzz 
                          then free_occ_t zzz t*free_occ_t zzz u 
                          else free_occ_t y t*free_occ_t zzz u+free_occ_t zzz t ))
                    (p_subst_sig (t_size t) (psubst y u) t
                     (subst_aux_7 x t (t_size t) p)))))
                 =plus (t_size (val_to_term (abstr x t)))
                  (free_occ_v y (abstr x t)*(minus (t_size u) 1)))
                (∀z0:Variable
                 .free_occ_t z0
                  (val_to_term
                   (abstr x
                    (pi1 pTerm
                     (λu0:pTerm
                      .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                       ∧(∀zzz:Variable
                         .free_occ_t zzz u0
                          =if veqb y zzz 
                           then free_occ_t zzz t*free_occ_t zzz u 
                           else free_occ_t y t*free_occ_t zzz u+free_occ_t zzz t ))
                     (p_subst_sig (t_size t) (psubst y u) t
                      (subst_aux_7 x t (t_size t) p)))))
                  =if veqb y z0 
                   then free_occ_v z0 (abstr x t)*free_occ_t z0 u 
                   else free_occ_v y (abstr x t)*free_occ_t z0 u
                            +free_occ_v z0 (abstr x t) )
                (Sig_inv_ind pTerm
                 (λu0:pTerm
                  .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                   ∧(∀z:Variable
                     .free_occ_t z u0
                      =if veqb y z 
                       then free_occ_t z t*free_occ_t z u 
                       else free_occ_t y t*free_occ_t z u+free_occ_t z t ))
                 (p_subst_sig (t_size t) (psubst y u) t
                  (subst_aux_7 x t (t_size t) p))
                 (λH31:Σu0:pTerm
                                  .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                                   ∧(∀z:Variable
                                     .free_occ_t z u0
                                      =if veqb y z 
                                       then free_occ_t z t*free_occ_t z u 
                                       else free_occ_t y t*free_occ_t z u+free_occ_t z t )
                  .True (*S
                   (t_size
                    (pi1 pTerm
                     (λu0:pTerm
                      .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                       ∧(∀zzz:Variable
                         .free_occ_t zzz u0
                          =if veqb y zzz 
                           then free_occ_t zzz t*free_occ_t zzz u 
                           else free_occ_t y t*free_occ_t zzz u+free_occ_t zzz t ))
                     H31))
                   =t_size (val_to_term (abstr x t))
                    +free_occ_v y (abstr x t)*(minus (t_size u) 1)*))
                 (λterm0:pTerm
                  .λH11:t_size term0=t_size t+free_occ_t y t*(t_size u-1)
                             ∧(∀z:Variable
                               .free_occ_t z term0
                                =if veqb y z 
                                 then free_occ_t z t*free_occ_t z u 
                                 else free_occ_t y t*free_occ_t z u+free_occ_t z t )
                   .λeq:p_subst_sig (t_size t) (psubst y u) t
                            (subst_aux_7 x t (t_size t) p)
                            =«term0,H11»
                    .eq_ind_r ℕ (t_size t+free_occ_t y t*(t_size u-1))
                     (λx0:ℕ
                      .λ_:x0=t_size t+free_occ_t y t*(t_size u-1)
                       .S x0
                        =t_size (val_to_term (abstr x t))
                         +free_occ_v y (abstr x t)*(t_size u-1))
                     (eq_ind_r bool false
                      (λx0:bool
                       .λ_:x0=false
                        .S (t_size t+free_occ_t y t*(t_size u-1))
                         =S
                          (t_size t+(if x0 then O else free_occ_t y t )*(t_size u-1)))
                      (let (clause_2117:
                              t_size term0=t_size t+free_occ_t y t*pred (t_size u)) ≝
                              rewrite_r ℕ (t_size u-O)
                              (λx0:ℕ.t_size term0=t_size t+free_occ_t y t*pred x0)
                              (rewrite_l ℕ (t_size u-1)
                               (λx0:ℕ.t_size term0=t_size t+free_occ_t y t*x0)
                               (proj1
                                (t_size term0=t_size t+free_occ_t y t*(t_size u-1))
                                (∀z:Variable
                                 .free_occ_t z term0
                                  =if veqb y z 
                                   then free_occ_t z t*free_occ_t z u 
                                   else free_occ_t y t*free_occ_t z u+free_occ_t z t )
                                H11)
                               (pred (t_size u-O)) (eq_minus_S_pred (t_size u) O))
                              (t_size u) (minus_n_O (t_size u)) in 
                       ?(*rewrite_r ℕ (pred (t_size u-O))
                       (λx0:ℕ
                        .S (t_size t+free_occ_t y t*x0)
                         =S (t_size t+free_occ_t y t*(t_size u-1)))
                       (rewrite_l ℕ (t_size u)
                        (λx0:ℕ
                         .S (t_size t+free_occ_t y t*pred x0)
                          =S (t_size t+free_occ_t y t*(t_size u-1)))
                        (rewrite_l ℕ (t_size term0)
                         (λx0:ℕ.S x0=S (t_size t+free_occ_t y t*(t_size u-1)))
                         (rewrite_r ℕ (pred (t_size u-O))
                          (λx0:ℕ.S (t_size term0)=S (t_size t+free_occ_t y t*x0))
                          (rewrite_l ℕ (t_size u)
                           (λx0:ℕ
                            .S (t_size term0)=S (t_size t+free_occ_t y t*pred x0))
                           (rewrite_l ℕ (t_size term0) (λx0:ℕ.S (t_size term0)=S x0)
                            (refl ℕ (S (t_size term0)))
                            (t_size t+free_occ_t y t*pred (t_size u)) clause_2117)
                           (t_size u-O) (minus_n_O (t_size u)))
                          (t_size u-1) (eq_minus_S_pred (t_size u) O))
                         (t_size t+free_occ_t y t*pred (t_size u)) clause_2117)
                        (t_size u-O) (minus_n_O (t_size u)))
                       (t_size u-1) (eq_minus_S_pred (t_size u) O)*))
                      (veqb y x) veq)
                     (t_size term0)
                     ( ?(*proj1 (t_size term0=t_size t+free_occ_t y t*(t_size u-1))
                      (∀z:Variable
                       .free_occ_t z term0
                        =if veqb y z 
                         then free_occ_t z t*free_occ_t z u 
                         else free_occ_t y t*free_occ_t z u+free_occ_t z t ) H11*))))
                (λz:Variable
                 .Sig_inv_ind pTerm
                  (λu0:pTerm
                   .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                    ∧(∀z0:Variable
                      .free_occ_t z0 u0
                       =if veqb y z0 
                        then free_occ_t z0 t*free_occ_t z0 u 
                        else free_occ_t y t*free_occ_t z0 u+free_occ_t z0 t ))
                  (p_subst_sig (t_size t) (psubst y u) t
                   (subst_aux_7 x t (t_size t) p))
                  (λH32:Σu0:pTerm
                                   .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                                    ∧(∀z0:Variable
                                      .free_occ_t z0 u0
                                       =if veqb y z0 
                                        then free_occ_t z0 t*free_occ_t z0 u 
                                        else free_occ_t y t*free_occ_t z0 u+free_occ_t z0 t )
                   .free_occ_t z
                    (val_to_term
                     (abstr x
                      (pi1 pTerm
                       (λu0:pTerm
                        .t_size u0=t_size t+free_occ_t y t*(t_size u-1)
                         ∧(∀zzz:Variable
                           .free_occ_t zzz u0
                            =if veqb y zzz 
                             then free_occ_t zzz t*free_occ_t zzz u 
                             else free_occ_t y t*free_occ_t zzz u+free_occ_t zzz t ))
                       H32)))
                    =if veqb y z 
                     then free_occ_v z (abstr x t)*free_occ_t z u 
                     else free_occ_v y (abstr x t)*free_occ_t z u
                              +free_occ_v z (abstr x t) )
                  (λterm0:pTerm
                   .λH13:t_size term0=t_size t+free_occ_t y t*(t_size u-1)
                              ∧(∀z0:Variable
                                .free_occ_t z0 term0
                                 =if veqb y z0 
                                  then free_occ_t z0 t*free_occ_t z0 u 
                                  else free_occ_t y t*free_occ_t z0 u+free_occ_t z0 t )
                    .λeq:p_subst_sig (t_size t) (psubst y u) t
                             (subst_aux_7 x t (t_size t) p)
                             =«term0,H13»
                     .bool_inv_ind (veqb y z)
                      (λH33:bool
                       .free_occ_t z (val_to_term (abstr x term0))
                        =if H33 
                         then free_occ_v z (abstr x t)*free_occ_t z u 
                         else free_occ_v y (abstr x t)*free_occ_t z u
                                  +free_occ_v z (abstr x t) )
                      (λveqbyz:veqb y z=true
                       .eq_ind_r bool false
                        (λx0:bool
                         .λ_:x0=false
                          .if x0 then O else free_occ_t z term0 
                           =(if x0 then O else free_occ_t z t )*free_occ_t z u)
                        (eq_ind_r bool true
                         (λx0:bool
                          .λ_:x0=true
                           .free_occ_t z term0
                            =if x0 
                             then free_occ_t z t*free_occ_t z u 
                             else free_occ_t y t*free_occ_t z u+free_occ_t z t 
                            →free_occ_t z term0=free_occ_t z t*free_occ_t z u)
                         (λth:free_occ_t z term0=free_occ_t z t*free_occ_t z u.th)
                         (veqb y z) veqbyz
                         (proj2 (t_size term0=t_size t+free_occ_t y t*(t_size u-1))
                          (∀z0:Variable
                           .free_occ_t z0 term0
                            =if veqb y z0 
                             then free_occ_t z0 t*free_occ_t z0 u 
                             else free_occ_t y t*free_occ_t z0 u+free_occ_t z0 t )
                          H13 z))
                        (veqb z x)
                        match veqb_true_to_eq y z
                         in And
                         return 
                        λ_:((veqb y z=true→y=z)∧(y=z→veqb y z=true))
                        .(veqb z x=false)
                         with 
                        [conj
                         (veq_to_eq:(veqb y z=true→y=z))
                          
                         (_:(y=z→veqb y z=true))⇒
                         eq_ind Variable y
                         (λx_1:Variable.λ_x_2:y=x_1.veqb x_1 x=false) veq z
                         (veq_to_eq veqbyz)])
                      (λveqbyz:veqb y z=false
                       .bool_inv_ind (veqb z x)
                        (λH34:bool
                         .if H34 then O else free_occ_t z term0 
                          =(if veqb y x then O else free_occ_t y t )*free_occ_t z u
                           +(if H34 then O else free_occ_t z t ))
                        (λveqbzx:veqb z x=true
                         .eq_ind_r bool false
                          (λx0:bool
                           .λ_:x0=false
                            .O=(if x0 then O else free_occ_t y t )*free_occ_t z u+O)
                          (eq_ind bool (fvb_t z u)
                           (λx_1:bool
                            .λ_x_2:fvb_t z u=x_1
                             .x_1=false→O=free_occ_t y t*free_occ_t z u+O)
                           (λfvz:fvb_t z u=false
                            .match 
                             proj1 (∀t0:pTerm.free_occ_t z t0=O↔fvb_t z t0=false)
                             (∀v:pValue.free_occ_v z v=O↔fvb_tv z v=false)
                             (free_occ_to_fv z) u
                              in And
                              return 
                             λ_:((free_occ_t z u=O→fvb_t z u=false)
                                    ∧(fvb_t z u=false→free_occ_t z u=O))
                             .(O=free_occ_t y t*free_occ_t z u+O)
                              with 
                             [conj
                              (_:(free_occ_t z u=O→fvb_t z u=false))
                               
                              (Hfin:(fvb_t z u=false→free_occ_t z u=O))⇒
                              eq_ind_r ℕ O (λx0:ℕ.λH34:x0=O.O=free_occ_t y t*x0+O)
                              (eq_ind_r ℕ O (λx0:ℕ.λH35:x0=O.O=x0+O)
                               (rewrite_l ℕ O (λx0:ℕ.O=x0) (refl ℕ O) (O+O)
                                (plus_O_n O))
                               (free_occ_t y t*O) (times_O (free_occ_t y t)))
                              (free_occ_t z u) (Hfin fvz)])
                           (fvb_t x u) (veqb_fv z x u veqbzx) fv)
                          (veqb y x) veq)
                        ?(*(λveqbzx:veqb z x=false
                         .eq_ind_r bool false
                          (λx0:bool
                           .λ_:x0=false
                            .free_occ_t z term0
                             =(if x0 then O else free_occ_t y t )*free_occ_t z u
                              +(if false then O else free_occ_t z t ))
                          (eq_ind_r bool false
                           (λx0:bool
                            .λ_:x0=false
                             .free_occ_t z term0
                              =if x0 
                               then free_occ_t z t*free_occ_t z u 
                               else free_occ_t y t*free_occ_t z u+free_occ_t z t 
                              →free_occ_t z term0
                               =free_occ_t y t*free_occ_t z u+free_occ_t z t)
                           (λH:free_occ_t z term0
                                  =free_occ_t y t*free_occ_t z u+free_occ_t z t
                            .H)
                           (veqb y z) veqbyz
                           ?(*(proj2
                            (t_size term0=t_size t+free_occ_t y t*(t_size u-1))
                            (∀z0:Variable
                             .free_occ_t z0 term0
                              =if veqb y z0 
                               then free_occ_t z0 t*free_occ_t z0 u 
                               else free_occ_t y t*free_occ_t z0 u+free_occ_t z0 t )
                            H13 z)*))
                          (veqb y x) veq)*))))») ])
   (refl bool (fvb_t x u)) (le_n (t_size (val_to_term (abstr x t)))))
  =val_to_term (abstr x (p_subst t (psubst y u)))))
    
    (************************)
    
    
    >fv

  
(**+++++++++++++++*)
(**+++++++++++++++*)
(**+++++++++++++++*)
  
  ] qed. 
*)

axiom p_subst_bound_irrelevance:
 ∀n, n', t, s. t_size t ≤ n →
  t_size t ≤ n' →
   p_subst_sig n s t ? = p_subst_sig n' s t ?.//qed.

lemma p_subst_distro0:
 ∀n1, n2, t1, t2, s.
  t_size t1 = n1 →
   t_size t2 = n2  →
   pi1 … (p_subst_sig (S (n1 + n2)) s (appl t1 t2) ?) = appl (pi1 … (p_subst_sig n1 s t1 ?)) (pi1 … (p_subst_sig n2 s t2 ?)).

[  #n1 #n2 #n #t1 #t2 #H1 #H2 whd in ⊢ (? ? % ?);  @eq_f2
  [ @eq_f @p_subst_bound_irrelevance] /2/
| normalize //
| //
| //
]
qed.

lemma p_subst_distro:
 ∀t1, t2, s. p_subst (appl t1 t2) s = appl (p_subst t1 s) (p_subst t2 s).

#t1 #t2 #s
change with (pi1 … (p_subst_sig (t_size (appl t1 t2)) s (appl t1 t2) ?)) in match (p_subst (appl t1 t2) s);
change with (pi1 … (p_subst_sig (t_size t1) s t1 ?)) in match (p_subst t1 s);
change with (pi1 … (p_subst_sig (t_size t2) s t2 ?)) in match (p_subst t2 s);
change with (S ((t_size t1) + (t_size t2))) in match (t_size (appl t1 t2));
@p_subst_distro0 // qed.
