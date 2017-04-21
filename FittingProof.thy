(*<*)
theory FittingProof  
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Fitting's Solution\<close>
  
(**In this section we consider Fitting's solution to the objections raised in his previous discussion of G\"odel's Argument (pp. 164-9), 
especially the problem of Modal Collapse, which has been metaphysically interpreted as implying a rejection of free will.
Since we are generally commited to the existence of free will (in a pre-theoretical sense), such a result is
philosophically unappealing and rather seen as a problem in the argument's formalisation.*)
(**This part of the book still leaves several details unspecified and the reader is thus compelled to fill in the gaps.
As a result, we came across some premises and theorems allowing for different formalisations and therefore leading to disparate implications.
Only some of those cases are shown here for illustrative purposes. The options chosen were those better suiting argument's validity.*)
  
subsection \<open>Implicit Extensionality Assumptions\<close>
  
(** Since Isabelle/HOL is extensional, extensionality principles are valid directly out of the box:*)  
lemma EXT: "\<forall>\<alpha>::\<langle>\<zero>\<rangle>. \<forall>\<beta>::\<langle>\<zero>\<rangle>. (\<forall>\<gamma>::\<zero>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_set: "\<forall>\<alpha>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. \<forall>\<beta>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. (\<forall>\<gamma>::\<langle>\<zero>\<rangle>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_intensional: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<downharpoonleft>(\<alpha>::\<up>\<zero> )))  \<^bold>\<downharpoonleft>(\<beta>::\<up>\<zero>) \<rfloor> \<longrightarrow> \<alpha> = \<beta>" by auto
lemma EXT_int_pred: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<down>(\<alpha>::\<up>\<langle>\<zero>\<rangle>))) \<^bold>\<down>(\<beta>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<alpha> = \<beta>" using ext by metis  
  
subsection \<open>General Definitions\<close>

(** The following technical definitions are needed only for type correctness. They are used to convert
 extensional objects into rigid intensional ones.*)  
abbreviation trivialExpansion::"bool\<Rightarrow>io" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> \<lambda>w. \<phi>"  
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") where
  "E! x  \<equiv> (\<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w)" 
  
consts positiveProperty::"\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>)"
abbreviation God_star::"\<up>\<langle>\<zero>\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> \<lparr>Y x\<rparr>)"

abbreviation Entailment::"\<up>\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>X z\<rparr> \<^bold>\<rightarrow> \<lparr>Y z\<rparr>)"
  
subsection \<open>Part I - God's Existence is Possible\<close>  
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and        (** Axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" and         (** Axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and  (** Axiom 11.5 *)
  T2: "\<lfloor>\<P> \<down>G\<rfloor>"                               (** Proposition 11.16 (modified)*)
        
lemma True nitpick[satisfy] oops (** Model found: axioms are consistent*)

    
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by fastforce
    
(** @{text "T1"} (Positive properties are possibly instantiated) can be formalised in two different ways:*)    
theorem T1a: "\<lfloor>\<^bold>\<forall>X::\<langle>\<zero>\<rangle>. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. \<lparr>X z\<rparr>)\<rfloor>" 
  using A1a A2 by blast (** this is the one used in the book*)
theorem T1b: "\<lfloor>\<^bold>\<forall>X::\<up>\<langle>\<zero>\<rangle>. \<P> \<down>X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. X z)\<rfloor>" 
  nitpick oops (** this one is also possible but not valid so we won't use it *)
    
(** Some interesting (non-) equivalences:*)
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<^bold>\<down>Q)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) Q)\<rfloor>"  by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>X) Q)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>Q)\<rfloor>" nitpick oops (** not equivalent! *)

    
(** @{text "T3"} (God exists possibly) can be formalised in two different ways, using a @{text "de re"} or a @{text "de dicto"} reading.*)
theorem T3_deRe: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T1a T2 by simp 
theorem T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" nitpick oops    (** countersatisfiable*)      

(** From the last two theorems, we think @{text "T3_deRe"} should be the version originally implied in the book,
 since @{text "T3_deDicto"} is not valid (unless @{text "T1b"} were valid but it isn't)*)
lemma assumes T1b: "\<lfloor>\<^bold>\<forall>X. \<P> \<down>X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. X z)\<rfloor>" 
   shows T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using assms T2 by simp
    
subsection \<open>Part II - God's Existence is Necessary if Possible\<close>
  
(** In this variant @{term "\<P>"} also designates rigidly, as shown in the last section.*)
axiomatization where
      A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      (** Axiom 11.11 *)
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
    
lemma True nitpick[satisfy] oops (** Model found: so far all axioms consistent*)

abbreviation essenceOf::"\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>") where
  "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z::\<langle>\<zero>\<rangle>. \<lparr>Z x\<rparr> \<^bold>\<rightarrow> Y \<Rrightarrow> Z)"
  
(** Theorem 11.20 - Informal Proposition 5 *)
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)\<rfloor>" using A1b by metis
(** Theorem 11.21 *)
theorem God_starIsEssential: "\<lfloor>\<^bold>\<forall>x. G* x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G*) x)\<rfloor>" by meson
    
abbreviation necExistencePred:: "\<up>\<langle>\<zero>\<rangle>" ("NE") where
  "NE x  \<equiv> \<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w"

(** Informal Axiom 5*)
axiomatization where
 A5: "\<lfloor>\<P> \<down>NE\<rfloor>"
 
lemma True nitpick[satisfy] oops (** Model found: so far all axioms consistent*)

(** Reminder: We use the down-arrow notation because it is more explicit. See (non-) equivalences above.*)
lemma "\<lfloor>\<^bold>\<exists> G \<^bold>\<leftrightarrow> \<^bold>\<exists> \<^bold>\<down>G\<rfloor>" by simp       
lemma "\<lfloor>\<^bold>\<exists>\<^sup>E G \<^bold>\<leftrightarrow> \<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" by simp    
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<leftrightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" by simp    
    
(** Theorem 11.26 (Informal Proposition 7) - (possibilist) existence of God implies necessary (actualist) existence. *)
(** There are two different ways of formalising this theorem. Both of them are proven valid:*)

(** First version:*)
theorem GodExImpliesNecEx_v1: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" 
proof -
{
  fix w 
  {
    assume "\<exists>x. G x w"
    then obtain g where 1: "G g w" ..
    hence "NE g w" using A5 by auto
    hence "\<forall>Y. (\<E> Y g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w" by simp
    hence "(\<E> (\<lambda>x. G x w) g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>(\<lambda>x. G x w) z\<rparr>)) w" by (rule allE)
    hence 2: "((\<E> \<down>\<^sub>1G) g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>E G)) w" using A4b by meson
    have  "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)) w" using GodIsEssential by (rule allE)
    hence  "(G g \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) g)) w" by (rule allE)
    hence  "G g w \<longrightarrow> (\<E> \<down>\<^sub>1G) g w" by simp
    from this 1 have 3: "(\<E> \<down>\<^sub>1G) g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule mp)
  }
  hence "(\<exists>x. G x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by simp
}
 thus ?thesis by (rule allI) 
qed
  
(** Second version (which can be proven directly by automated tools using last version):*)
theorem GodExImpliesNecEx_v2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>"
  using A4a GodExImpliesNecEx_v1 by metis
    
    
(** Compared to Goedel's argument, the following theorems can be proven in @{text "K"} logic (note that S5 no longer needed): *)

(** Theorem 11.27 - Informal Proposition 8 *) 
theorem possExImpliesNecEx_v1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>"
  using GodExImpliesNecEx_v1 T3_deRe  by metis
theorem possExImpliesNecEx_v2: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>"
  using GodExImpliesNecEx_v2 by blast

(** Corollaries: *)    
lemma T4_v1:  "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>"
  using possExImpliesNecEx_v1 by simp
lemma T4_v2:  "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>"
  using possExImpliesNecEx_v2 by simp
    
    
subsection \<open>Conclusion - Necessary Existence of God\<close>        
    
(** Version I - @{text "de dicto"} reading: *)    
lemma GodNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>"
  using GodExImpliesNecEx_v1 T3_deRe by fastforce (** Corollary 11.28*)
lemma God_starNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G*\<rfloor>"
  using GodNecExists_v1 GodDefsAreEquivalent by simp
lemma "\<lfloor>\<^bold>\<box>(\<lambda>X. \<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G*\<rfloor>"
  using God_starNecExists_v1 by simp (**@{text "de dicto"} shown here explicitly*)
    
(** Version II - @{text "de re"} reading: *)    
lemma GodNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>"
  using T3_deRe T4_v2 by blast
lemma God_starNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G*\<rfloor>"
  using GodNecExists_v2 GodDefsAreEquivalent by simp

subsection \<open>Modal Collapse\<close>
(** Modal Collapse is countersatisfiable even in @{text "S5"}. Note that countermodels with a cardinality of one 
for the domain of ground-level objects are found by Nitpick (the countermodel shown in the book has cardinality of two).*)
    
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countermodel found in @{text "K"}*)
    
axiomatization where
   S5: "equivalence aRel" (**assume @{text "S5"} logic *)
   
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countermodel also found in @{text "S5"}*)

(*<*)
end
(*>*)
