(*<*)
theory ExamplesHOML
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)

section \<open>Book Examples\<close>
  
(** In this section we verify that our embedded logic works as intended by proving the examples provided in the book.
 In many cases, for good mesure, we consider further theorems derived from the original ones. We were able to confirm that all results
 (proves or counterexamples) agree with our expectations.*)
  
subsection \<open>Modal Logic - Syntax and Semantics (Chapter 7)\<close>
 
subsubsection \<open>Considerations Regarding @{text "\<beta>\<eta>"}-redex  (p. 94)\<close>
  
(** @{text "\<beta>\<eta>"}-redex is valid for non-relativized (intensional or extensional) terms (because they designate rigidly): *)
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<zero>)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp    
(** @{text "\<beta>\<eta>"}-redex is valid for relativized terms as long as no modal operators occur inside the predicate abstract: *)
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>) \<^bold>\<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<phi> \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" by simp
(** @{text "\<beta>\<eta>"}-redex is non-valid for relativized terms when modal operators are present: *)
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) \<^bold>\<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" nitpick oops   (** countersatisfiable *)
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<diamond>\<phi> \<alpha>) \<^bold>\<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<diamond>\<phi> \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" nitpick oops   (** countersatisfiable *)
    
(** Example 7.13, p. 96:*)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>"
  nitpick[card 't=1, card i=2] oops (** nitpick finds same counterexample as book*)
(** with other types for @{term "P"}: *)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
    
(** Example 7.14, p. 98:*)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
(** with other types for @{term "P"}: *)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
    
(** Example 7.15, p. 99:*)
lemma "\<lfloor>\<^bold>\<box>(P (c::\<up>\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<up>\<zero>. \<^bold>\<box>(P x))\<rfloor>" by auto
(** with other types for @{term "P"}: *)
lemma "\<lfloor>\<^bold>\<box>(P (c::\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<zero>. \<^bold>\<box>(P x))\<rfloor>" by auto
lemma "\<lfloor>\<^bold>\<box>(P (c::\<langle>\<zero>\<rangle>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<langle>\<zero>\<rangle>. \<^bold>\<box>(P x))\<rfloor>" by auto
    
(** Example 7.16, p. 100:*)
lemma "\<lfloor>\<^bold>\<box>(P \<^bold>\<downharpoonleft>(c::\<up>\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<zero>. \<^bold>\<box>(P x))\<rfloor>" 
  nitpick[card 't=2, card i=2] oops (** counterexample with two worlds found *)
    
(** Example 7.17, p. 101:*)
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>\<zero>. (\<lambda>x::\<zero>.  \<^bold>\<box>((\<lambda>y::\<zero>.  x \<^bold>\<approx> y) \<^bold>\<downharpoonleft>Z)) \<^bold>\<downharpoonleft>Z\<rfloor>" 
  nitpick[card 't=2, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>\<^bold>\<forall>z::\<zero>.  (\<lambda>x::\<zero>.  \<^bold>\<box>((\<lambda>y::\<zero>.  x \<^bold>\<approx> y)  z)) z\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>\<zero>. (\<lambda>X::\<up>\<zero>. \<^bold>\<box>((\<lambda>Y::\<up>\<zero>. X \<^bold>\<approx> Y)  Z)) Z\<rfloor>" by simp
    
subsubsection \<open>Exercises (p. 101)\<close>
    
(** For Exercises 7.1 and 7.2 see variations on Examples 7.13 and 7.14 above. *)
(** Exercise 7.3: *)    
lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<^bold>\<exists>X::\<up>\<zero>. \<^bold>\<diamond>(P \<^bold>\<downharpoonleft>X))\<rfloor>" by auto
lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>(P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<^bold>\<exists>X::\<up>\<langle>\<zero>\<rangle>. \<^bold>\<diamond>(P \<^bold>\<down>X))\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *) (* TODO why?*)
(** Exercise 7.4: *)  
lemma "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x::\<zero>. (\<lambda>Y. Y x) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x. (\<lambda>Y. \<^bold>\<diamond>(Y x)) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)    
    
(** For Exercise 7.5 see Example 7.17 above. *)
    
    
subsection \<open>Miscellaneous Matters (Chapter 9)\<close>

subsubsection \<open>Equality Axioms (Subsection 1.1)\<close>
    
(** Example 9.1: *)
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<^bold>\<downharpoonleft>(p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx> x) \<^bold>\<downharpoonleft>p))\<rfloor>" 
  by auto (** using normal equality *)
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<^bold>\<downharpoonleft>(p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>L x) \<^bold>\<downharpoonleft>p))\<rfloor>" 
  by auto (** using Leibniz equality *)
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X  (p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>C x) p))\<rfloor>" 
  by simp  (** using equality as defined for individual concepts *)

    
subsubsection \<open>Extensionality (Subsection 1.2)\<close>
    
(** In the book, extensionality is assumed (globally) for extensional terms. Extensionality is however
   already implicit in Isabelle/HOL as we can see: *)    
lemma EXT: "\<forall>\<alpha>::\<langle>\<zero>\<rangle>. \<forall>\<beta>::\<langle>\<zero>\<rangle>. (\<forall>\<gamma>::\<zero>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_set: "\<forall>\<alpha>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. \<forall>\<beta>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. (\<forall>\<gamma>::\<langle>\<zero>\<rangle>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" 
  by auto

(** Extensionality for intensional terms is also already implicit in the HOL embedding: *)
lemma EXT_int: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<downharpoonleft>(\<alpha>::\<up>\<zero> )))  \<^bold>\<downharpoonleft>(\<beta>::\<up>\<zero>)\<rfloor> \<longrightarrow> \<alpha> = \<beta>" by auto
lemma EXT_int_pred: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<down>(\<alpha>::\<up>\<langle>\<zero>\<rangle>))) \<^bold>\<down>(\<beta>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<alpha> = \<beta>" 
  using ext by metis
    
    
subsubsection \<open>D@{text "e Re"} and @{text "De Dicto"} (Subsection 2)\<close>

(** @{text "De re"} is equivalent to @{text "de dicto"} for non-relativized (extensional or intensional) terms: *)
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<zero>))   \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<zero>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<langle>\<zero>\<rangle>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp

(** @{text "De re"} is not equivalent to @{text "de dicto"} for relativized (intensional) terms: *)    
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" 
  nitpick[card 't=2, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>(\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
  
(** Proposition 9.6 - Equivalences between @{text "de dicto"} and @{text "de re"}: *)
abbreviation deDictoEquDeRe::"\<up>\<langle>\<up>\<zero>\<rangle>" 
  where "deDictoEquDeRe \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
abbreviation deDictoImplDeRe::"\<up>\<langle>\<up>\<zero>\<rangle>" 
  where "deDictoImplDeRe \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
abbreviation deReImplDeDicto::"\<up>\<langle>\<up>\<zero>\<rangle>" 
  where "deReImplDeDicto \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
  
abbreviation deDictoEquDeRe_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deDictoEquDeRe_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deDictoImplDeRe_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deDictoImplDeRe_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deReImplDeDicto_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deReImplDeDicto_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"

(* The following are valid only when using global consequence: *)
(* TODO: solvers need some help to find the proofs
lemma "\<lfloor>deDictoImpliesDeRe (\<tau>::\<up>\<zero>)\<rfloor> \<longrightarrow> \<lfloor>deReImpliesDeDicto \<tau>\<rfloor>" oops
lemma "\<lfloor>deReImpliesDeDicto (\<tau>::\<up>\<zero>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImpliesDeRe \<tau>\<rfloor>" oops
lemma "\<lfloor>deDictoImpliesDeRe_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>deReImpliesDeDicto_pred \<tau>\<rfloor>" oops
lemma "\<lfloor>deReImpliesDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImpliesDeRe_pred \<tau>\<rfloor>" oops*)
    
subsubsection \<open>Rigidity (Subsection 3)\<close>
    
(** Rigidity for intensional individuals: *)    
abbreviation rigidIndiv::"\<up>\<langle>\<up>\<zero>\<rangle>" where
  "rigidIndiv \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<downharpoonleft>\<tau>)) \<^bold>\<downharpoonleft>\<tau>"
(** Rigidity for intensional predicates: *)    
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
  "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
  
(** Proposition 9.8 - We can prove it using local consequence (global consequence follows directly). *)  
lemma "\<lfloor>rigidIndiv (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> deReImplDeDicto \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> rigidIndiv \<tau>\<rfloor>" by auto
lemma "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> deReImplDeDicto_pred \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> rigidPred \<tau>\<rfloor>" by auto
    
    
subsubsection \<open>Stability Conditions (Subsection 4)\<close>
    
axiomatization where
S5: "equivalence aRel"  (** We use the Sahlqvist correspondence for improved performance*)
    
(** Definition 9.10 - Stability: *)
abbreviation stabilityA::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityA \<tau> \<equiv> \<^bold>\<forall>\<alpha>. (\<tau> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<tau> \<alpha>)"
abbreviation stabilityB::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityB \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<diamond>(\<tau> \<alpha>) \<^bold>\<rightarrow> (\<tau> \<alpha>)"

(** Proposition 9.10 - Note it is valid only for global consequence.*)
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityB \<tau>\<rfloor>" using S5 by blast    
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> stabilityB \<tau>\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable for local consequence*)
    
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityA \<tau>\<rfloor>" using S5 by blast    
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> stabilityA \<tau>\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable for local consequence*)
    
(** Theorem 9.11 - Note that we can prove even local consequence. *)
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   

(*<*)
end
(*>*)