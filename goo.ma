include "underline_readback.ma".

lemma irrelevant:
 ∀n,n',s,t,H,H'. pi1 … (pif_subst_sig (S n) s t H) = pi1 … (pif_subst_sig (S n') s t H').
 #n #n' * #v #M #t
 whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
 whd in match (match ? in pifSubst with [ _ ⇒ ? ]);
 cases t (* dovrebbe essere elim, ma vuole predicato mutuo! *)
 [ *
   [ #v' normalize in ⊢ (% → % → ?); #H #H' @eq_f
     cut (∀HHT',HHF'.
     (pif_subst_sig (S n) (psubst v M) (val_to_term (pvar v')) H
  = match veqb v v'
    return λb. veqb v v' = b → 1 ≤ S n' →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb v v' = true.
        λp: 1 ≤ S n'.
         «M, HHT' H p»
     | false ⇒ λH: veqb v v' = false.
        λp: 1 ≤ S n'.
         «val_to_term (pvar v'), HHF' H p»
     ] (refl bool (veqb v v')) H')
     )
  [2: #UU @UU] #HHT' #HHF'
  check (pif_subst_sig (S n') (psubst v M) (val_to_term (pvar v')) H')
  cut (∀HHT,HHF.
   eq
   (Σu:pifTerm
  .t_size u
   =t_size (val_to_term (pvar v'))
    +free_occ_t
     v
     (val_to_term (pvar v'))
     *(t_size
       M
       -1)
   ∧(∀z:Variable
     .free_occ_t z u
      =if veqb
            v z 
       then free_occ_t z (val_to_term (pvar v'))
                *free_occ_t z
                 M 
       else free_occ_t
                v
                (val_to_term (pvar v'))
                *free_occ_t z
                 M
                +free_occ_t z (val_to_term (pvar v')) )
   )
   (match veqb v v'
    return λb. veqb v v' = b → 1 ≤ S n →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb v v' = true.
        λp: 1 ≤ S n.
         «M, HHT H p»
     | false ⇒ λH: veqb v v' = false.
        λp: 1 ≤ S n.
         «val_to_term (pvar v'), HHF H p»
     ] (refl bool (veqb v v')) H)
   (match veqb v v'
    return λb. veqb v v' = b → 1 ≤ S n' →
    Σu: pifTerm. ?
    with
     [ true ⇒ λH: veqb v v' = true.
        λp: 1 ≤ S n'.
         «M, ?(*HHT' H p*)»
     | false ⇒ λH: veqb v v' = false.
        λp: 1 ≤ S n'.
         «val_to_term (pvar v'), ?(*HHF' H p*)»
     ] (refl bool (veqb v v')) H')
  )
  [4: #UU @UU
  |skip
  |skip ] #HHT #HHF
  cases (veqb v v') in HHT HHF HHT' HHF' ⊢ %; normalize
  #HHT #HHF #HHT' #HHF' %
