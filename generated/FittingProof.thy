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
lemma EXT_intensional: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<downharpoonleft>(\<alpha>::\<up>O )))  \<^bold>\<downharpoonleft>(\<beta>::\<up>O) \<rfloor> \<longrightarrow> \<alpha> = \<beta>" by auto
lemma EXT_int_pred: "\<lfloor>(\<lambda>x. ((\<lambda>y. x\<^bold>\<approx>y) \<^bold>\<down>(\<alpha>::\<up>\<langle>O\<rangle>))) \<^bold>\<down>(\<beta>::\<up>\<langle>O\<rangle>)\<rfloor> \<longrightarrow> \<alpha> = \<beta>" using ext by metis  
  
subsection \<open>General Definitions\<close>

text\<open>  Following enables using extensional objects as if they were rigid intensional objects (needed only for type correctness): \<close>  
abbreviation trivialExpansion::"bool\<Rightarrow>io" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> \<lambda>w. \<phi>"
  
abbreviation existencePredicate::"\<up>\<langle>O\<rangle>" ("E!") where
  "E! x  \<equiv> (\<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w)" 
  
consts positiveProperty::"\<up>\<langle>\<langle>O\<rangle>\<rangle>" ("\<P>")
abbreviation God::"\<up>\<langle>O\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>)"
abbreviation God_star::"\<up>\<langle>O\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> \<lparr>Y x\<rparr>)"

abbreviation Entailment::"\<up>\<langle>\<langle>O\<rangle>,\<langle>O\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<lparr>X z\<rparr> \<^bold>\<rightarrow> \<lparr>Y z\<rparr>)"
  
subsection \<open>Part I - God's existence is possible\<close>  
  
text\<open>  Following Scott's proposal we take T2 directly as an axiom.  \<close>
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and        --\<open>  Axiom 11.3A  \<close>
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" and         --\<open>  Axiom 11.3B  \<close>
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and  --\<open>  Axiom 11.5  \<close>
  T2: "\<lfloor>\<P> \<down>G\<rfloor>"                               --\<open>  Proposition 11.16 (modified) \<close>
        
lemma True nitpick[satisfy] oops --\<open>  Axioms are consistent \<close>

    
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by fastforce
    
text\<open>  T1 (Positive properties are possibly instantiated) can be formalized in two different ways: \<close>    
theorem T1a: "\<lfloor>\<^bold>\<forall>X::\<langle>O\<rangle>. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. \<lparr>X z\<rparr>)\<rfloor>" using A1a A2 by blast --\<open>  The one used in the book \<close>
theorem T1b: "\<lfloor>\<^bold>\<forall>X::\<up>\<langle>O\<rangle>. \<P> \<down>X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. X z)\<rfloor>" nitpick oops --\<open>  Since this one is not valid, we won't use it  \<close>
    
text\<open>  Interesting (non-) equivalences: \<close>
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>E \<^bold>\<down>Q)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) Q)\<rfloor>"  by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>X) Q)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E (Q::\<up>\<langle>O\<rangle>) \<^bold>\<leftrightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>Q)\<rfloor>" nitpick oops --\<open>  not equivalent!  \<close>

    
text\<open>  T3 (God exists possibly) can be formalized in two different ways, using a de-re or a de-dicto reading. \<close>
theorem T3_deRe: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T1a T2 by simp 
theorem T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" nitpick oops    --\<open>  countersatisfiable \<close>      

text\<open>  T3_deRe should be the version implied in the book, because T3_deDicto is not valid unless T1b (from above) were valid \<close>
lemma assumes T1b: "\<lfloor>\<^bold>\<forall>X. \<P> \<down>X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ez. X z)\<rfloor>" 
   shows T3_deDicto: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using assms T2 by simp
    
subsection \<open>Part II - God's existence is necessary if possible\<close>

text\<open>  P satisfies so-called stability conditions (Page 124). This means P designates rigidly (an essentialist assumption!).  \<close>
axiomatization where
      A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      --\<open>  Axiom 11.11  \<close>
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
    
lemma True nitpick[satisfy] oops --\<open>  So far all axioms consistent \<close>

abbreviation essenceOf::"\<up>\<langle>\<langle>O\<rangle>,O\<rangle>" ("\<E>") where
  "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z::\<langle>O\<rangle>. \<lparr>Z x\<rparr> \<^bold>\<rightarrow> Y \<Rrightarrow> Z)" --\<open>  The one used in the book \<close>
  
text\<open>  Theorem 11.20 - Informal Proposition 5  \<close>
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)\<rfloor>" using A1b by metis
text\<open>  Theorem 11.21  \<close>
theorem God_starIsEssential: "\<lfloor>\<^bold>\<forall>x. G* x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G*) x)\<rfloor>" by meson
    
abbreviation necExistencePred:: "\<up>\<langle>O\<rangle>" ("NE") where
  "NE x  \<equiv> \<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. \<lparr>Y z\<rparr>)) w" --\<open>  the one used in the book  \<close>

text\<open>  Informal Axiom 5 \<close>
axiomatization where
 A5: "\<lfloor>\<P> \<down>NE\<rfloor>"
 
lemma True nitpick[satisfy] oops --\<open>  So far all axioms consistent \<close>

text\<open>  Reminder: We use the down-arrow notation because it is more explicit - see (non-) equivalences above. \<close>
lemma "\<lfloor>\<^bold>\<exists> G \<^bold>\<leftrightarrow> \<^bold>\<exists> \<^bold>\<down>G\<rfloor>" by simp       
lemma "\<lfloor>\<^bold>\<exists>\<^sup>E G \<^bold>\<leftrightarrow> \<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" by simp    
lemma "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<leftrightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" by simp    
    
text\<open>  Theorem 11.26 (Informal Proposition 7) - (possibilist) existence of God implies necessary (actualist) existence.  \<close>
text\<open>  There are two different ways of formalizing this theorem. Both of them are proved valid: \<close>

text\<open>  First version: \<close>
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
  
text\<open>  Second version (which can be proven directly by automated tools using last version): \<close>
theorem GodExImpliesNecEx_v2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>"
  using A4a GodExImpliesNecEx_v1 by metis
    
    
text\<open>  Compared to Goedel's argument, the following theorems can be proven in K (S5 no longer needed!):  \<close>

text\<open>  Theorem 11.27 - Informal Proposition 8  \<close> 
theorem possExImpliesNecEx_v1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using GodExImpliesNecEx_v1 T3_deRe  by metis
theorem possExImpliesNecEx_v2: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G)\<rfloor>" using GodExImpliesNecEx_v2 by blast

text\<open>  Corollaries:  \<close>    
lemma T4_v1:  "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using possExImpliesNecEx_v1 by simp
lemma T4_v2:  "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using possExImpliesNecEx_v2 by simp
    
    
subsection \<open>Conclusion - Necessary (actualist) existence of God (Corollary 11.28)\<close>        
    
text\<open>  Version I - De dicto reading:  \<close>    
lemma GodNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G\<rfloor>" using GodExImpliesNecEx_v1 T3_deRe by fastforce
lemma God_starNecExists_v1: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E \<^bold>\<down>G*\<rfloor>" using GodNecExists_v1 GodDefsAreEquivalent by simp
lemma "\<lfloor>\<^bold>\<box>(\<lambda>X. \<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G*\<rfloor>" using God_starNecExists_v1 by simp --\<open>  De dicto reading shown explicitly \<close>
    
text\<open>  Version II - De re reading:  \<close>    
lemma GodNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G\<rfloor>" using T3_deRe T4_v2 by blast
lemma God_starNecExists_v2: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>E X) \<^bold>\<down>G*\<rfloor>" using GodNecExists_v2 GodDefsAreEquivalent by simp

subsection \<open>Modal Collapse\<close>
text\<open>  Modal Collapse is countersatisfiable even in S5. Counterexamples with cardinality one for the domain
of ground-level objects are found by Nitpick:  \<close>
    
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[card 't=1, card i=2] oops
    
axiomatization where
   S5: "equivalence aRel"
   
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick[card 't=1, card i=2] oops

(*<*)
end
(*>*)
