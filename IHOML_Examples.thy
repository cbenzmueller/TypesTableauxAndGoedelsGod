(*<*)
theory IHOML_Examples
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)

section \<open>Textbook Examples\<close>
  
(** In this section we provide further evidence that our embedded logic works as intended by proving the examples discussed in the book.
 In many cases, we consider further theorems which we derived from the original ones. We were able to confirm that all results
 (proofs or counterexamples) agree with Fitting's claims.*)
  
subsection \<open>Modal Logic - Syntax and Semantics (Chapter 7)\<close>

(**Note: In what follows, we will call a term \emph{relativized} if it is of the form @{text "\<down>\<phi>"}
(i.e. an intensional term preceded by the \emph{extension-of} operator), otherwise it is \emph{non-relativized}.
Relativized terms are non-rigid.*)
  
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
  
(** In Fitting's book (p. 118), extensionality is assumed (globally) for extensional terms. While Fitting introduces 
the following extensionality principles as axioms, they are already implicitly valid in Isabelle/HOL: *)    
lemma EXT: "\<forall>\<alpha>::\<langle>\<zero>\<rangle>. \<forall>\<beta>::\<langle>\<zero>\<rangle>. (\<forall>\<gamma>::\<zero>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_set: "\<forall>\<alpha>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. \<forall>\<beta>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. (\<forall>\<gamma>::\<langle>\<zero>\<rangle>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" 
  by auto
    
subsubsection \<open>\emph{De Re} and \emph{De Dicto} (Subsection 2)\<close>

(** \emph{De re} is equivalent to \emph{de dicto} for non-relativized (extensional or intensional) terms: *)
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<zero>))   \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<zero>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<langle>\<zero>\<rangle>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp

(** \emph{De re} is not equivalent to \emph{de dicto} for relativized (intensional) terms: *)    
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)\<rfloor>" 
  nitpick[card 't=2, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>(\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
  
(** Proposition 9.6 - If we can prove one side of the equivalence, then we can prove the other (p. 120): *)
abbreviation deDictoImplDeRe::"\<up>\<zero>\<Rightarrow>io" 
  where "deDictoImplDeRe \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
abbreviation deReImplDeDicto::"\<up>\<zero>\<Rightarrow>io" 
  where "deReImplDeDicto \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
abbreviation deReEquDeDicto::"\<up>\<zero>\<Rightarrow>io" 
  where "deReEquDeDicto \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<downharpoonleft>\<tau>)"
    
abbreviation deDictoImplDeRe_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deDictoImplDeRe_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deReImplDeDicto_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deReImplDeDicto_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deReEquDeDicto_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deReEquDeDicto_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"

(** We can prove local consequence:*)
lemma AimpB: "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> deDictoImplDeRe \<tau>\<rfloor>"
  by force (** for individuals*)
lemma AimpB_p: "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> deDictoImplDeRe_pred \<tau>\<rfloor>"
  by force (** for predicates*)

(** And global consequence follows directly (since local consequence implies global consequence, as shown before):*)
lemma "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImplDeRe \<tau>\<rfloor>"
  using AimpB by (rule localImpGlobalCons) (** for individuals*)
lemma "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImplDeRe_pred \<tau>\<rfloor>"
  using AimpB_p by (rule localImpGlobalCons) (** for predicates*)
       
    
subsubsection \<open>Rigidity (Subsection 3)\<close>
    
(** (Local) rigidity for intensional individuals: *)    
abbreviation rigidIndiv::"\<up>\<langle>\<up>\<zero>\<rangle>" where
  "rigidIndiv \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<downharpoonleft>\<tau>)) \<^bold>\<downharpoonleft>\<tau>"
(** (Local) rigidity for intensional predicates: *)    
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
  "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
  
(** Proposition 9.8 - An intensional term is rigid if and only if the \emph{de re/de dicto} distinction vanishes.
Note that we can prove this theorem for local consequence (global consequence follows directly). *)  
lemma "\<lfloor>rigidIndiv (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> deReEquDeDicto \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> rigidIndiv \<tau>\<rfloor>" by auto
lemma "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> deReEquDeDicto_pred \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> rigidPred \<tau>\<rfloor>" by auto
   
subsubsection \<open>Stability Conditions (Subsection 4)\<close>
    
axiomatization where
 S5: "equivalence aRel" (**using Sahlqvist correspondence for improved performance*)
    
(** Definition 9.10 - Stability conditions come in pairs: *)
abbreviation stabilityA::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityA \<tau> \<equiv> \<^bold>\<forall>\<alpha>. (\<tau> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<tau> \<alpha>)"
abbreviation stabilityB::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityB \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<diamond>(\<tau> \<alpha>) \<^bold>\<rightarrow> (\<tau> \<alpha>)"

(** Proposition 9.10 - In an \emph{S5} modal logic both stability conditions are equivalent.*)
(** The last proposition holds for global consequence:*)  
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityB \<tau>\<rfloor>" using S5 by blast    
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityA \<tau>\<rfloor>" using S5 by blast    
(** But it does not hold for local consequence:*)      
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> stabilityB \<tau>\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable*)
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> stabilityA \<tau>\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable*)
    
(** Theorem 9.11 - A term is rigid if and only if it satisfies the stability conditions. Note that
 we can prove this theorem for local consequence (global consequence follows directly). *)
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
(** \pagebreak*)
(*<*)
end
(*>*)
