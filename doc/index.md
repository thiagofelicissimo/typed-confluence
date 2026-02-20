
The following list provides links between the main definitions and theorems in the paper and their counterparts in the formalization. We tried our best to add these local links to the PDF to ease reviewing, but unfortunately we did not manage to do it, as local links in PDFs seem to be very problematic. Therefore, links in the submitted PDF have been disabled.

As explained in the paper, to deal with the extensions to the initial type system while avoiding duplicating the code, our formalization takes place in a theory containing all the rules, while using a [system of flags](coqdoc/TypedConfluence.theories.Flags.html) that allow turning on or off the rules specific to the extensions



### Typing (Section 2)
- [Raw core terms](coqdoc/TypedConfluence.theories.autosubst.Ast.html#Core.term)
- [Fig 1 (Typing rules)](coqdoc/TypedConfluence.theories.Typing.html#typing)
- [Fig 2 (Conversion rules)](coqdoc/TypedConfluence.theories.Typing.html#conversion)
- [Stability under renaming](coqdoc/TypedConfluence.theories.BasicMetaTheory.html#typing_conversion_ren)
- [Stability under substitution](coqdoc/TypedConfluence.theories.BasicMetaTheory.html#typing_conversion_subst)
- [Validity](coqdoc/TypedConfluence.theories.BasicMetaTheory.html#validity_gen)
- [Uniqueness of types](coqdoc/TypedConfluence.theories.BasicMetaTheory.html#type_sort_unique)

### Confluence (Section 3)

- [Fig 3 (Orthogonal reduction)](coqdoc/TypedConfluence.theories.Confluence.html#ortho_red)
- [Lemma 3.1, point 1 (Reflexivity)](coqdoc/TypedConfluence.theories.Confluence.html#ortho_refl)
- [Lemma 3.1, point 2 (Inclusion in Conversion)](coqdoc/TypedConfluence.theories.Confluence.html#ortho_to_conv)
- [Lemma 3.1, point 3 (Stability Under Substitution)](coqdoc/TypedConfluence.theories.Confluence.html#subst_ortho)
- [Lemma 3.1, point 4 (Context Conversion)](coqdoc/TypedConfluence.theories.Confluence.html#ortho_conv_in_ctx)
- [Theorem 3.2 (Diamond property)](coqdoc/TypedConfluence.theories.Confluence.html#diamond)
- [Corollary 3.3 (Confluence)](coqdoc/TypedConfluence.theories.Confluence.html#confluence)
- [Corollary 3.4 (Church-Rosser property)](coqdoc/TypedConfluence.theories.Confluence.html#CR_equiv)
- [Proposition 3.5 (equiv included in ≡)](coqdoc/TypedConfluence.theories.Confluence.html#equiv_to_conv)
- [Proposition 3.6 (≡ included in equiv)](coqdoc/TypedConfluence.theories.Confluence.html#conv_to_equiv)
- [Theorem 3.7 (Injectivity and non-confusion of type formers)](coqdoc/TypedConfluence.theories.Confluence.html#type_formers_inj)
- [Lemma 3.8 (Result of canonical type reduction)](coqdoc/TypedConfluence.theories.Confluence.html#type_former_redd)

### Conversion checking (Section 4)

- [Fig 4 (Erasure function)](coqdoc/TypedConfluence.theories.ConversionChecking.html#erasure)
- [Fig 5 (Erased reduction)](coqdoc/TypedConfluence.theories.ConversionChecking.html#red)
- [Proposition 4.1 (Subject reduction)](coqdoc/TypedConfluence.theories.ConversionChecking.html#subject_reduction)
- [Fig 6 (Normals and neutrals)](coqdoc/TypedConfluence.theories.ConversionChecking.html#Nf)
- [Lemma 4.2](coqdoc/TypedConfluence.theories.ConversionChecking.html#nf_is_ne)
- [Proposition 4.3 (Irreducible implies normal)](coqdoc/TypedConfluence.theories.ConversionChecking.html#irred_to_Nf)
- [Proposition 4.4 (Erased eqality to conversion)](coqdoc/TypedConfluence.theories.ConversionChecking.html#eq_erased_nf)
- [Lemma 4.5 (Erased eqality to conversion)](coqdoc/TypedConfluence.theories.ConversionChecking.html#eq_erased)
- [Theorem 4.6 (Soundness of conversion checking)](coqdoc/TypedConfluence.theories.ConversionChecking.html#convcheck_sound)
- [Counter-example of Remark 4.1](coqdoc/TypedConfluence.theories.Misc.CounterExample.html)
- [Lemma 4.7](coqdoc/TypedConfluence.theories.ConversionChecking.html#ortho_red_to_eq)
- [Theorem 4.8 (Completeness of conversion checking)](coqdoc/TypedConfluence.theories.ConversionChecking.html#convcheck_complete)

### Bidirectional typing (Section 5)

- [Fig 7 (User-level syntax)](coqdoc/TypedConfluence.theories.TypeChecking.html#cterm)
- [Fig 8 (Bidirectional typing rules)](coqdoc/TypedConfluence.theories.TypeChecking.html#infer)
- [Theorem 5.1 (Soundness of Bidirectional Typing)](coqdoc/TypedConfluence.theories.TypeChecking.html#sound)
- [Theorem 5.2 (Completeness of Bidirectional Typing)](coqdoc/TypedConfluence.theories.TypeChecking.html#completeness_check)
- [Lemma 5.3](coqdoc/TypedConfluence.theories.TypeChecking.html#completeness)


### Extensions (Section 6)

Most links are the same as the ones given above.

- [Deriving dependent J from non-dependent J](coqdoc/TypedConfluence.theories.Misc.DepJFromJ.html)
