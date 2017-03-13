(*<*)
theory ExamplesHOML
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)

section \<open>Examples in book\<close>
  
subsection \<open>Chapter 7 - Modal Logic - Syntax and Semantics\<close>
 
subsubsection \<open>beta/eta-redex Considerations (page 94)\<close>
  
text\<open>  beta/eta-redex is valid for non-relativized (intensional or extensional) terms (because they designate rigidly):  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<up>O)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::O)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<up>O)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::O)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp    
text\<open>  beta/eta-redex is valid for relativized terms as long as no modal operators occur inside the predicate abstract:  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>) \<^bold>\<downharpoonleft>(\<tau>::\<up>O)) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" by simp
text\<open>  beta/eta-redex is non-valid for relativized terms when modal operators are present:  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) \<^bold>\<downharpoonleft>(\<tau>::\<up>O)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" nitpick oops   --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<diamond>\<phi> \<alpha>) \<^bold>\<downharpoonleft>(\<tau>::\<up>O)) \<^bold>\<leftrightarrow> (\<^bold>\<diamond>\<phi> \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" nitpick oops   --\<open>  countersatisfiable  \<close>
    
text\<open>  Example 7.13 page 96: \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  nitpick finds same counterexample as book \<close>
text\<open>  with other types for P:  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>O\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>O\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<langle>O\<rangle>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<langle>O\<rangle>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>)\<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>)\<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
    
text\<open>  Example 7.14 page 98: \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
text\<open>  with other types for P:  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>O\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>O\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<langle>O\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<langle>O\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>)\<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>)\<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
    
text\<open>  Example 7.15 page 99: \<close>
lemma "\<lfloor>\<^bold>\<box>(P (c::\<up>O)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<up>O. \<^bold>\<box>(P x))\<rfloor>" by auto
text\<open>  for other types:  \<close>
lemma "\<lfloor>\<^bold>\<box>(P (c::O)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::O. \<^bold>\<box>(P x))\<rfloor>" by auto
lemma "\<lfloor>\<^bold>\<box>(P (c::\<langle>O\<rangle>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<langle>O\<rangle>. \<^bold>\<box>(P x))\<rfloor>" by auto
    
text\<open>  Example 7.16 page 100: \<close>
lemma "\<lfloor>\<^bold>\<box>(P \<^bold>\<downharpoonleft>(c::\<up>O)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::O. \<^bold>\<box>(P x))\<rfloor>" nitpick[card 't=2, card i=2] oops --\<open>  countersatisfiable (using only two worlds!)  \<close>
    
text\<open>  Example 7.17 page 101: \<close>
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>O. (\<lambda>x::O.  \<^bold>\<box>((\<lambda>y::O.  x \<^bold>\<approx> y) \<^bold>\<downharpoonleft>Z)) \<^bold>\<downharpoonleft>Z\<rfloor>" nitpick[card 't=2, card i=2] oops --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>\<^bold>\<forall>z::O.  (\<lambda>x::O.  \<^bold>\<box>((\<lambda>y::O.  x \<^bold>\<approx> y)  z)) z\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>O. (\<lambda>X::\<up>O. \<^bold>\<box>((\<lambda>Y::\<up>O. X \<^bold>\<approx> Y)  Z)) Z\<rfloor>" by simp
    
subsubsection \<open>Exercises page 101\<close>
    
text\<open>  For Exercises 7.1 and 7.2 see variations on Examples 7.13 and 7.14 above.  \<close>
text\<open>  Exercise 7.3:  \<close>    
lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>(P::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> (\<^bold>\<exists>X::\<up>O. \<^bold>\<diamond>(P \<^bold>\<downharpoonleft>X))\<rfloor>" by auto
lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>(P::\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<^bold>\<exists>X::\<up>\<langle>O\<rangle>. \<^bold>\<diamond>(P \<^bold>\<down>X))\<rfloor>" nitpick[card 't=1, card i=2] oops (* non-valid variation - TODO why?*)
text\<open>  Exercise 7.4:  \<close>  
lemma "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x::O. (\<lambda>Y. Y x) \<^bold>\<down>(P::\<up>\<langle>O\<rangle>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x. (\<lambda>Y. \<^bold>\<diamond>(Y x)) \<^bold>\<down>P)\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>    
    
text\<open>  For Exercise 7.5 see Example 7.17 above.  \<close>
    
    
subsection \<open>Chapter 9 - Miscellaneous Matters\<close>

subsubsection \<open>(1.1) Equality\<close>
    
text\<open>  Example 9.1:  \<close>
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<^bold>\<downharpoonleft>(p::\<up>O))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx> x) \<^bold>\<downharpoonleft>p))\<rfloor>" by auto --\<open>  using normal equality  \<close>
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<^bold>\<downharpoonleft>(p::\<up>O))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>L x) \<^bold>\<downharpoonleft>p))\<rfloor>" by auto --\<open>  using Leibniz equality  \<close>
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X  (p::\<up>O))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>C x) p))\<rfloor>" by simp  --\<open>  variation using equality for individual concepts  \<close>

    
subsubsection \<open>(1.2) Extensionality\<close>
    
text\<open>  In the book, extensionality is assumed (globally) for extensional terms. Extensionality is however
   already implicit in Isabelle/HOL:  \<close>    
lemma EXT: "\<forall>\<alpha>::\<langle>O\<rangle>. \<forall>\<beta>::\<langle>O\<rangle>. (\<forall>\<gamma>::O. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_set: "\<forall>\<alpha>::\<langle>\<langle>O\<rangle>\<rangle>. \<forall>\<beta>::\<langle>\<langle>O\<rangle>\<rangle>. (\<forall>\<gamma>::\<langle>O\<rangle>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto

text\<open>  Extensionality for intensional terms is also already implicit in the HOL embedding:  \<close>
lemma EXT_intensional:      "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<downharpoonleft>(\<alpha>::\<up>O )))  \<^bold>\<downharpoonleft>(\<beta>::\<up>O) \<rfloor> \<longrightarrow> \<alpha> = \<beta>" by auto
lemma EXT_intensional_pred: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<down>(\<alpha>::\<up>\<langle>O\<rangle>))) \<^bold>\<down>(\<beta>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<alpha> = \<beta>" using ext by metis
    
    
subsubsection \<open>(2) De re & de dicto\<close>

text\<open>  de re is equivalent to de dicto for non-relativized (extensional or intensional) terms:  \<close>
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::O))   \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>O))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<langle>O\<rangle>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<langle>O\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp

text\<open>  de re is not equivalent to de dicto for relativized (intensional) terms:  \<close>    
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>(\<tau>::\<up>O)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" nitpick[card 't=2, card i=2] oops --\<open>  countersatisfiable  \<close>
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>(\<tau>::\<up>\<langle>O\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable  \<close>
  
text\<open>  Proposition 9.6 - Equivalences between de dicto and de re:  \<close>
abbreviation deDictoEquDeRe::"\<up>\<langle>\<up>O\<rangle>" where "deDictoEquDeRe \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
abbreviation deDictoImpliesDeRe::"\<up>\<langle>\<up>O\<rangle>" where "deDictoImpliesDeRe \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
abbreviation deReImpliesDeDicto::"\<up>\<langle>\<up>O\<rangle>" where "deReImpliesDeDicto \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
  
abbreviation deDictoEquDeRe_pred::"('t\<Rightarrow>io)\<Rightarrow>io" where "deDictoEquDeRe_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deDictoImpliesDeRe_pred::"('t\<Rightarrow>io)\<Rightarrow>io" where "deDictoImpliesDeRe_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deReImpliesDeDicto_pred::"('t\<Rightarrow>io)\<Rightarrow>io" where "deReImpliesDeDicto_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"

text\<open>  The following are valid only when using global consequence:  \<close>
text\<open>  (TODO: solvers need some help to find the proofs)  \<close>
lemma "\<lfloor>deDictoImpliesDeRe (\<tau>::\<up>O)\<rfloor> \<longrightarrow> \<lfloor>deReImpliesDeDicto \<tau>\<rfloor>" oops
lemma "\<lfloor>deReImpliesDeDicto (\<tau>::\<up>O)\<rfloor> \<longrightarrow> \<lfloor>deDictoImpliesDeRe \<tau>\<rfloor>" oops
lemma "\<lfloor>deDictoImpliesDeRe_pred (\<tau>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>deReImpliesDeDicto_pred \<tau>\<rfloor>" oops
lemma "\<lfloor>deReImpliesDeDicto_pred (\<tau>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImpliesDeRe_pred \<tau>\<rfloor>" oops
    
subsubsection \<open>(3) Rigidity\<close>
    
text\<open>  Rigidity for intensional individuals:  \<close>    
abbreviation rigidIndiv::"\<up>\<langle>\<up>O\<rangle>" where
  "rigidIndiv \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<downharpoonleft>\<tau>)) \<^bold>\<downharpoonleft>\<tau>"
text\<open>  ... and for intensional predicates:  \<close>    
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
  "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
  
text\<open>  Proposition 9.8 - We can prove it using local consequence (global consequence follows directly).  \<close>  
lemma "\<lfloor>rigidIndiv (\<tau>::\<up>O) \<^bold>\<rightarrow> deReImpliesDeDicto \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImpliesDeDicto (\<tau>::\<up>O) \<^bold>\<rightarrow> rigidIndiv \<tau>\<rfloor>" by auto
lemma "\<lfloor>rigidPred (\<tau>::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> deReImpliesDeDicto_pred \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImpliesDeDicto_pred (\<tau>::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> rigidPred \<tau>\<rfloor>" by auto
    
    
subsubsection \<open>(4) Stability Conditions\<close>
    
axiomatization where
S5: "equivalence aRel"  --\<open>  We use the Sahlqvist correspondence for improved performance \<close>
    
text\<open>  Definition 9.10 - Stability:  \<close>
abbreviation stabilityA::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityA \<tau> \<equiv> \<^bold>\<forall>\<alpha>. (\<tau> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<tau> \<alpha>)"
abbreviation stabilityB::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityB \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<diamond>(\<tau> \<alpha>) \<^bold>\<rightarrow> (\<tau> \<alpha>)"

text\<open>  Proposition 9.10 - Note it is valid only for global consequence. \<close>
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityB \<tau>\<rfloor>" using S5 by blast    
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> stabilityB \<tau>\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable for local consequence \<close>
    
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityA \<tau>\<rfloor>" using S5 by blast    
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>O\<rangle>) \<^bold>\<rightarrow> stabilityA \<tau>\<rfloor>" nitpick[card 't=1, card i=2] oops --\<open>  countersatisfiable for local consequence \<close>
    
text\<open>  Theorem 9.11 - Note that we can prove even local consequence!  \<close>
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>O\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<langle>O\<rangle>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   

(*<*)
end
(*>*)
