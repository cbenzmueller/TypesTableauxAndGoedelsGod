(*<*)
theory AndersonProof  
imports HOML_int
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Anderson's Alternative\<close>
  
text\<open> In this last section we consider Anderson's Alternative to the objections previously shown, as exposed in the last
part of the textbook (pp. 169-171) \<close>
  
subsection \<open>General Definitions\<close>
 
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w"
  
consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
  
text\<open>  Godlike, Anderson Version (Definition 11.33)  \<close>    
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G\<^sup>A") where "G\<^sup>A \<equiv> \<lambda>x. \<^bold>\<forall>Y. (\<P> Y) \<^bold>\<leftrightarrow> \<^bold>\<box>(Y x)"
  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"
  
subsection \<open>Part I - God's Existence is Possible\<close>  
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and          --\<open>  Axiom 11.3A  \<close>
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   --\<open>  Axiom 11.5  \<close>
  T2: "\<lfloor>\<P> G\<^sup>A\<rfloor>"                                 --\<open>  Proposition 11.16  \<close>
        
lemma True nitpick[satisfy] oops --\<open>  Model found: axioms are consistent \<close>
    
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" 
  using A1a A2 by blast  --\<open>  Positive properties are possibly instantiated \<close>  
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T1 T2 by simp  --\<open>  God exists possibly  \<close>  
    
    
subsection \<open>Part II - God's Existence is Necessary if Possible\<close>
        
text\<open>  @{text "\<P>"} now satisfies only one of the stability conditions (p. 124). But since the argument uses an @{text "S5"} logic, 
the other stability condition is implied. Therefore @{text "\<P>"} becomes rigid.  \<close>
axiomatization where
  A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      --\<open>  Axiom 11.11  \<close>
      
text\<open>  Axiomatizing semantic frame conditions for different modal logics (via \emph{Sahlqvist correspondence}).
 All axioms together imply an @{term "S5"} logic. \<close>
axiomatization where
 refl: "reflexive aRel" and
 tran: "transitive aRel" and
 symm: "symmetric aRel"
 
lemma True nitpick[satisfy] oops --\<open>  Model found: so far all axioms consistent \<close>
 
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
 "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"

lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" 
  using A4a symm by auto --\<open> note only symmetry is needed (@{term "B"} axiom)  \<close>
lemma "\<lfloor>rigidPred \<P>\<rfloor>" 
  using A4a A4b by blast --\<open> @{term "\<P>"} is therefore rigid in a @{term "B"} logic \<close>
  
    
subsubsection \<open>Theorems\<close>

text\<open>  Essence, Anderson Version (Definition 11.34) \<close>
abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>\<^sup>A") where
  "\<E>\<^sup>A Y x \<equiv> (\<^bold>\<forall>Z. \<^bold>\<box>(Z x) \<^bold>\<leftrightarrow> Y \<Rrightarrow> Z)"

      
text\<open>  Necessary Existence, Anderson Version (Definition 11.35)  \<close>  
abbreviation necessaryExistencePred::"\<up>\<langle>\<zero>\<rangle>" ("NE\<^sup>A") 
  where "NE\<^sup>A x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E>\<^sup>A Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"
  
(*abbreviation beingIdenticalTo::"\<zero>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("id") where
  "id x  \<equiv> (\<lambda>y. y\<^bold>\<approx>x)"  note that @{term "id"} is a rigid predicate*)  

    
text\<open>  Theorem 11.36  \<close>
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)\<rfloor>" sorry (*using A1a A2 A4a T2 refl tran symm by force*)


text\<open>  Axiom 11.37 (Anderson's Version of 11.25) \<close>
axiomatization where 
 A5: "\<lfloor>\<P> NE\<^sup>A\<rfloor>"
 
lemma True nitpick[satisfy] oops --\<open>  Model found: so far all axioms consistent \<close>
 
text\<open>  Theorem 11.38 - Possibilist existence of God implies necessary actualist existence:  \<close> 
theorem GodExistenceImpliesNecExistence: "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>"
proof -
{
  fix w 
  {
    assume "\<exists>x. G\<^sup>A x w"
    then obtain g where 1: "G\<^sup>A g w" ..
    hence "NE\<^sup>A g w" using A5 by blast                     --\<open>  Axiom 11.25 \<close>
    hence "\<forall>Y. (\<E>\<^sup>A Y g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w" by simp
    hence 2: "(\<E>\<^sup>A G\<^sup>A g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule allE)
    have  "(\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)) w" using GodIsEssential
      by (rule allE)     --\<open>  GodIsEssential follows from Axioms 11.11 and 11.3B  \<close>
    hence  "(G\<^sup>A g \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A g)) w" by (rule allE)
    hence  "G\<^sup>A g w \<longrightarrow> \<E>\<^sup>A G\<^sup>A g w"  by blast
    from this 1 have 3: "\<E>\<^sup>A G\<^sup>A g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule mp)
  }
  hence "(\<exists>x. G\<^sup>A x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G\<^sup>A x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by simp
}
 thus ?thesis by (rule allI) 
qed
    
text\<open>  Some useful rules: \<close>    
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp

text\<open>  Anderson's Version of Theorem 11.27  \<close> 
theorem possExistenceImpliesNecEx: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" --\<open> local consequence \<close>
proof -
  have "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using GodExistenceImpliesNecExistence 
    by simp --\<open>  follows from Axioms 11.11, 11.25 and 11.3B \<close>
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using symm tran by metis
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by simp
  thus ?thesis by (rule modal_trans)
qed

lemma T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using possExistenceImpliesNecEx 
    by simp --\<open>  global consequence \<close>
  
text\<open>  Conclusion - Necessary (actualist) existence of God:  \<close>    
lemma GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T3 T4 by metis    
    
subsubsection \<open>Modal Collapse\<close>
  
text\<open>  Modal Collapse is countersatisfiable  \<close>
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick oops
     
(*<*)
end
(*>*)
