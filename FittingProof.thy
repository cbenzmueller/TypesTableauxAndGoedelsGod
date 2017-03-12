(*<*)
theory FittingProof  
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Fitting's Proof (pages 165-166)\<close>
  
subsection \<open>Implicit extensionality assumptions in Isabelle/HOL\<close>
  
lemma EXT: "\<forall>\<alpha>::\<langle>O\<rangle>. \<forall>\<beta>::\<langle>O\<rangle>. (\<forall>\<gamma>::O. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_set: "\<forall>\<alpha>::\<langle>\<langle>O\<rangle>\<rangle>. \<forall>\<beta>::\<langle>\<langle>O\<rangle>\<rangle>. (\<forall>\<gamma>::\<langle>O\<rangle>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_intensional:      "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<downharpoonleft>(\<alpha>::\<up>O )))  \<^bold>\<downharpoonleft>(\<beta>::\<up>O) \<rfloor> \<longrightarrow> \<alpha> = \<beta>" by auto
lemma EXT_intensional_pred: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<down>(\<alpha>::\<up>\<langle>O\<rangle>))) \<^bold>\<down>(\<beta>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<alpha> = \<beta>" using ext by metis  
  
subsection \<open>General Definitions\<close>

(** Enables using extensional objects as if they were rigid intensional objects (needed only for type correctness)*)  
abbreviation trivialExpansion::"bool\<Rightarrow>io" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> \<lambda>w. \<phi>"
  
abbreviation existencePredicate::"\<up>\<langle>O\<rangle>" ("E!") where "E! x  \<equiv> (\<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w)" 
consts positiveProperty::"\<up>\<langle>\<langle>O\<rangle>\<rangle>" ("\<P>")
abbreviation God::"\<up>\<langle>O\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>)"
abbreviation God_star::"\<up>\<langle>O\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> \<lparr>Y x\<rparr>)"

abbreviation Entailment::"\<up>\<langle>\<langle>O\<rangle>,\<langle>O\<rangle>\<rangle>" (infix "\<succeq>" 60) where "X \<succeq> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>X z\<rparr> \<^bold>\<rightarrow> \<lparr>Y z\<rparr>)"
  
subsection \<open>Part I - God's existence is possible\<close>  
  
(** Following Scott's proposal we take T2 directly as an axiom *)
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and        (** Axiom 11.3A *)
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" and         (** Axiom 11.3B *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<succeq> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and  (** Axiom 11.5 *)
  T2: "\<lfloor>\<P> \<down>G\<rfloor>"                               (** Proposition 11.16 (modified)*)
        
lemma True nitpick[satisfy] oops (** Axioms are consistent*)

    
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by fastforce
    
(** T1 (Positive properties are possibly instantiated) can be formalized in two different ways*)    
theorem T1a: "\<lfloor>\<^bold>\<forall>X::\<langle>O\<rangle>. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. \<lparr>X z\<rparr>)\<rfloor>" using A1a A2 by blast (** The one used in the book*)
theorem T1b: "\<lfloor>\<^bold>\<forall>X::\<up>\<langle>O\<rangle>. \<P> \<down>X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. X z)\<rfloor>" nitpick oops         (** Since this one is not valid, we won't use it *)
    
(** Some interesting (non-) equivalences (analogously for \<diamond>-operator) *)
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<^bold>\<down>Q)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) Q)\<rfloor>"  by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>X) Q)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>Q)\<rfloor>" nitpick oops (** not equivalent! *)

    
(** T3 (God exists possibly) can be formalized in two different ways: using a de-re or a de-dicto reading *)
    
theorem T3_deRe: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T1a T2 by simp      (* this should be the version implied in the book because...*)
theorem T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" nitpick oops                   (* ...this one is not valid, unless...*)
    
lemma assumes T1b: "\<lfloor>\<^bold>\<forall>X. \<P> \<down>X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. X z)\<rfloor>" 
   shows T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using assms T2 by simp        (* ... T1b (from above) were valid *)

    
subsection \<open>Part II - God's existence is necessary if possible\<close>

(** \<P> satisfies so-called stability conditions (Page 124). This means \<P> designates rigidly (an essentialist assumption!) *)
axiomatization where
      A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      (** Axiom 11.11 *)
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
    
lemma True nitpick[satisfy] oops (** So far all axioms consistent*)

abbreviation essenceOf::"\<up>\<langle>\<langle>O\<rangle>,O\<rangle>" ("\<E>") where "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z::\<langle>O\<rangle>. \<lparr>Z x\<rparr> \<^bold>\<rightarrow> Y \<succeq> Z)"                   (** The one used in the book*)
  
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)\<rfloor>" using A1b by metis  (** Theorem 11.20 - Informal Proposition 5 *)
theorem God_starIsEssential: "\<lfloor>\<^bold>\<forall>x. G* x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G*) x)\<rfloor>" by meson  (** Theorem 11.21 *)
    
abbreviation necExistencePred:: "\<up>\<langle>O\<rangle>" ("NE")  where "NE x  \<equiv> \<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w" (** the one used in the book *)

(** Informal Axiom 5*)
axiomatization where
 A5: "\<lfloor>\<P> \<down>NE\<rfloor>"
 
lemma True nitpick[satisfy] oops (** So far all axioms consistent*)

(** Reminder: We use the \<^bold>\<down> notation because it is more explicit - see (non-) equivalences above*)
lemma "\<lfloor>\<^bold>\<exists> G \<^bold>\<leftrightarrow> \<^bold>\<exists> \<^bold>\<down>G\<rfloor>" by simp       
lemma "\<lfloor>\<^bold>\<exists>\<^sup>E G \<^bold>\<leftrightarrow> \<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" by simp    
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<leftrightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" by simp    
    
(** Theorem 11.26 (Informal Proposition 7) - (possibilist) existence of God implies necessary (actualist) existence *)
(** There are two different ways of formalizing this theorem. Both of them are proved valid.*)

(** First version*)
theorem GodExistenceImpliesNecExistence_v1: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" 
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
  
(** Second version (which can be proven directly by automated tools)*)
theorem GodExistenceImpliesNecExistence_v2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>"
  using A4a GodExistenceImpliesNecExistence_v1 by metis
    
    
(** Compared to Gödel's argument, the following theorems can be proven in K (S5 no longer needed!) *)

(** Theorem 11.27 - Informal Proposition 8 *) 
theorem possibleExistenceImpliesNecEx_v1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using GodExistenceImpliesNecExistence_v1 T3_deRe  by metis
theorem possibleExistenceImpliesNecEx_v2:  "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>" using GodExistenceImpliesNecExistence_v2 by blast

(** Corollaries *)    
lemma T4_v1:  "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using possibleExistenceImpliesNecEx_v1 by simp
lemma T4_v2:  "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using possibleExistenceImpliesNecEx_v2 by simp
    
    
subsection \<open>Conclusion - Necessary (actualist) existence of God (Corollary 11.28)\<close>        
    
(** Version I - De dicto reading *)    
lemma GodNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using GodExistenceImpliesNecExistence_v1 T3_deRe by fastforce
lemma God_starNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G*\<rfloor>" using GodNecExists_v1 GodDefsAreEquivalent by simp
lemma "\<lfloor>\<^bold>\<box>(\<lambda>X. \<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G*\<rfloor>" using God_starNecExists_v1 by simp (** De dicto reading shown explicitly*)
    
(** Version II - De re reading *)    
lemma GodNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T3_deRe T4_v2 by blast
lemma God_starNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G*\<rfloor>" using GodNecExists_v2 GodDefsAreEquivalent by simp

subsection \<open>Modal Collapse\<close>
(** Modal Collapse is countersatisfiable even in S5. Counterexamples with cardinality 1 for the domain
of ground-level objects are found by Nitpick *)
    
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[card 'a=1, card i=2] oops
    
axiomatization where
   S5: "equivalence aRel"
   
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[card 'a=1, card i=2] oops