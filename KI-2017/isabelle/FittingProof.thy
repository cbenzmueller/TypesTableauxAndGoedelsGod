(*<*)
theory FittingProof  
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Fitting's Variant\<close>
  
(**In this section we consider Fitting's solution to the objections raised in his discussion of G\"odel's Argument (@{cite "Fitting"}, pp. 164-9), 
especially the problem of modal collapse, which has been metaphysically interpreted as implying a rejection of free will.
In G\"odel's variant, positiveness and essence were thought of as predicates applying to \emph{intensional} properties and
correspondingly formalized using intensional types for their arguments (@{text "\<up>\<langle>\<up>\<langle>e\<rangle>\<rangle>"} and @{text "\<up>\<langle>\<up>\<langle>e\<rangle>,e\<rangle>"} respectively).
In this variant, Fitting chooses to reformulate these definitions using \emph{extensional} types (@{text "\<up>\<langle>\<langle>e\<rangle>\<rangle>"} and @{text "\<up>\<langle>\<langle>e\<rangle>,e\<rangle>"}) instead,
and makes the corresponding adjustments to the rest of the argument (to ensure type correctness).
This has some philosophical repercussions; e.g. while we could say before that honesty (as concept) was a
positive property, now we can only talk of its extension at some world and say of some group of people
that they are honest (necessarily honest, in fact, because @{text "\<P>"} has also been proven `rigid' in this variant).\footnote{
In what follows, the `@{text "\<lparr>_\<rparr>"}' parentheses are used to convert an extensional object into its `rigid'
intensional counterpart (e.g. @{text "\<lparr>\<phi>\<rparr> \<equiv> \<lambda>w. \<phi>"}).}*)
  
  consts Positiveness::"\<up>\<langle>\<langle>e\<rangle>\<rangle>" ("\<P>")
  abbreviation Entails::"\<up>\<langle>\<langle>e\<rangle>,\<langle>e\<rangle>\<rangle>" (infix"\<Rrightarrow>"(*<*)60(*>*)) where "X\<Rrightarrow>Y \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Az. \<lparr>X z\<rparr>\<^bold>\<rightarrow>\<lparr>Y z\<rparr>)"
  abbreviation Essence::"\<up>\<langle>\<langle>e\<rangle>,e\<rangle>" ("\<E>") where "\<E> Y x \<equiv> \<lparr>Y x\<rparr> \<^bold>\<and> (\<^bold>\<forall>Z.\<lparr>Z x\<rparr>\<^bold>\<rightarrow>(Y\<Rrightarrow>Z))"
(*<*)
  abbreviation Existence::"\<up>\<langle>e\<rangle>" ("E!") where "E! x \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ay. y\<^bold>\<approx>x) w"
  abbreviation God::"\<up>\<langle>e\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<lparr>Y x\<rparr>)"
  abbreviation necessaryExistencePredicate :: "\<up>\<langle>e\<rangle>" ("NE") where
    "NE x  \<equiv> \<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Az. \<lparr>Y z\<rparr>)) w"

  axiomatization where
    A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and
    A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>" and 
    A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and
    T2: "\<lfloor>\<P> \<down>G\<rfloor>"  and                        
    A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" and
    A5: "\<lfloor>\<P> \<down>NE\<rfloor>"
    
  lemma True nitpick[satisfy] oops (**model found: all axioms consistent*)
          
  lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
  lemma "\<lfloor>rigid \<P>\<rfloor>" using A4a A4b by blast (**@{text "\<P>"} designates rigidly*)
(*>*)
      
(**Axioms and theorems remain essentially the same. Particularly (T2) @{text "\<lfloor>\<P> \<down>G\<rfloor>"} and (A5) @{text "\<lfloor>\<P> \<down>NE\<rfloor>"}
  work with \emph{relativized} extensional terms now.*)
  
  theorem T1: "\<lfloor>\<^bold>\<forall>X::\<langle>e\<rangle>. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Az. \<lparr>X z\<rparr>)\<rfloor>" using A1a A2 by blast 
  theorem T3deRe: "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>A X) \<^bold>\<down>G\<rfloor>" using T1 T2 by simp
  lemma GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)\<rfloor>" using A1b by metis
      
(**The following theorem could be formalized in two variants\footnote{Fitting's original
treatment in @{cite "Fitting"} left several details unspecified and
we had to fill in the gaps by choosing appropriate formalization variants (see @{cite "J35"} for details).}
(drawing on the \emph{de re/de dicto} distinction).
We prove both of them valid and show how the argument splits, culminating in two non-equivalent versions
of the conclusion, both of which are proven valid.*)
  lemma T4v1: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>A \<^bold>\<down>G\<rfloor>" proof - (**not shown*)
(*<*)
  {
    fix w 
    {
      assume "\<exists>x. G x w"
      then obtain g where 1: "G g w" ..
      hence "NE g w" using A5 by auto
      hence "\<forall>Y. (\<E> Y g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Az. \<lparr>Y z\<rparr>)) w" by simp
      hence "(\<E> (\<lambda>x. G x w) g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Az. \<lparr>(\<lambda>x. G x w) z\<rparr>)) w" by (rule allE)
      hence 2: "((\<E> \<down>\<^sub>1G) g w) \<longrightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>A G)) w" using A4b by meson
      have  "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) x)) w" using GodIsEssential by (rule allE)
      hence  "(G g \<^bold>\<rightarrow> ((\<E> \<down>\<^sub>1G) g)) w" by (rule allE)
      hence  "G g w \<longrightarrow> (\<E> \<down>\<^sub>1G) g w" by simp
      from this 1 have 3: "(\<E> \<down>\<^sub>1G) g w" by (rule mp)
      from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>A G) w" by (rule mp)
    }
    hence "(\<exists>x. G x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>A G) w" by (rule impI)
    hence "((\<^bold>\<exists>x. G x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>A G) w" by simp
  }
   thus ?thesis by (rule allI) 
  qed
(*>*)
    
  lemma T4v2: "\<lfloor>\<^bold>\<exists> \<^bold>\<down>G \<^bold>\<rightarrow> ((\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>A X) \<^bold>\<down>G)\<rfloor>" using A4a T4v1 by metis
      
(**In contrast to G\"odel's version (as presented by Fitting), the following theorems can be proven in logic \emph{K}
   (the \emph{S5} axioms are no longer needed).*)    
  lemma T5v1:"\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> \<^bold>\<down>G\<rfloor>\<longrightarrow>\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>A \<^bold>\<down>G\<rfloor>" using T4v1 T3deRe by metis
  lemma T5v2:"\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>\<^sup>A X) \<^bold>\<down>G\<rfloor> \<longrightarrow> \<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>A X) \<^bold>\<down>G\<rfloor>" using T4v2 by blast
      
(**Necessary Existence of God (\emph{de dicto} and \emph{de re} readings).*)    
  lemma GodNecExists_deDicto: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>A \<^bold>\<down>G\<rfloor>" using T3deRe T4v1 by blast
  lemma GodNecExists_deRe: "\<lfloor>(\<lambda>X. \<^bold>\<box>\<^bold>\<exists>\<^sup>A X) \<^bold>\<down>G\<rfloor>" using T3deRe T5v2 by blast
  
(**Modal collapse is countersatisfiable even in \emph{S5}. Note that countermodels with a cardinality of \emph{one} 
  for the domain of individuals are found by \emph{Nitpick} (the countermodel shown in Fitting's book has cardinality of \emph{two}).*)
  lemma "equivalence aRel\<Longrightarrow>\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi>\<^bold>\<rightarrow> \<^bold>\<box>\<Phi>\<rfloor>" nitpick[card e=1, card w=2] oops
(*<*)
end
(*>*)
