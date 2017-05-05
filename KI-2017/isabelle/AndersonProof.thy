(*<*)
theory AndersonProof  
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Anderson's Variant\<close>
(**In this final section, we verify Anderson's emendation of G\"odel's argument @{cite "anderson90:_some_emend_of_goedel_ontol_proof"},
as presented by Fitting (@{cite "Fitting"}, pp. 169-171). In the previous variants `indifferent' properties were not possible,
 every property had to be either positive or negative. Anderson makes room for `indifferent' properties by
 dropping axiom \emph{A1b} (@{text "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<rightharpoondown>X)\<rfloor>"}). Consequently, he also changed some definitions
 in order to ensure argument's validity.*)
(*<*)  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where (**def changed*)
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)" 
consts Positiveness::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
abbreviation Existence::"\<up>\<langle>\<zero>\<rangle>" ("E!") where "E! x \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w"
(*>*)
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G\<^sup>A") where "G\<^sup>A \<equiv> \<lambda>x. \<^bold>\<forall>Y. (\<P> Y) \<^bold>\<leftrightarrow> \<^bold>\<box>(Y x)"
abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>\<^sup>A") where
  "\<E>\<^sup>A Y x \<equiv> (\<^bold>\<forall>Z. \<^bold>\<box>(Z x) \<^bold>\<leftrightarrow> Y \<Rrightarrow> Z)"
  
(** There is now the requirement, a Godlike being must have positive properties \emph{necessarily}.
For the definition of essence, Scott's addition, that the essence of an object 
actually applies to the object, is dropped. A necessity operator has been introduced instead.
\footnote{Without Scott's addition @{cite "ScottNotes"}, G\"odel's original axiom system can be proven inconsistent as shown by @{cite "C55"}.} *)
(*<*)
abbreviation necessaryExistencePred::"\<up>\<langle>\<zero>\<rangle>" ("NE\<^sup>A")
  where "NE\<^sup>A x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E>\<^sup>A Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and          (* Axiom 11.3A *)
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   (* Axiom 11.5 *)
  T2: "\<lfloor>\<P> G\<^sup>A\<rfloor>"        and
  A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"  and
  A5: "\<lfloor>\<P> NE\<^sup>A\<rfloor>" 
(*>*)
(**The rest of the ontological argument is essentially similar to G\"odel's variant (which also needs \emph{S5} axioms).*)
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by blast
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T1 T2 by simp
(*<*)
axiomatization where (** We again postulate our \emph{S5} axioms:*)
 refl: "reflexive aRel" and tran: "transitive aRel" and symm: "symmetric aRel"

lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A4a symm by auto
lemma "\<lfloor>rigidPred \<P>\<rfloor>" using A4a A4b by blast (**@{text "\<P>"} is rigid*)
lemma True nitpick[satisfy] oops (** model found: so far all axioms consistent*)
(*>*)   
(**If g is God-like, the property of being God-like is its essence.
\footnote{As shown before, this theorem's proof could be completely automatized for G\"odel's and Fitting's variants.
For Anderson's version however, we had to provide Isabelle with some help based on the corresponding natural-language proof 
given by Anderson (see @{cite "anderson90:_some_emend_of_goedel_ontol_proof"} Theorem 2*, p. 296)}*)
(*Anderson's Proof: Suppose that g is God-like* and necessarily has a property Q. Then
by definition (of "God-like*"), that property is positive. But necessarily, if
Q is positive, then if anything is God-like*, then it has Q -again by the
definition of "God-like* ," together with the fact that if something has a
property necessarily, then it has the property. But if a property is positive,
then it is necessarily positive (Axiom 4). Hence, if Q is positive, then it is
entailed by being God-like* (by modal logic-as in the original Theorem 2).
But Q is positive and hence is entailed by being God-like*. Thus we have
proved that if an entity is God-like* and has a property essentially, then that
property is entailed by the property of being God-like*.
Suppose a property Q is entailed by the property of being God-like*. Then
Q is positive by Axioms 2 and 3* and therefore, since g is God-like*, g has
Q necessarily (by the definition of "God-like*"). Hence, if something is
God-like*, it has a property essentially if and only if that property is entailed
by being God-like-i.e., God-likeness* is an essence* of that thing.
Q.E.D.*)
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)\<rfloor>" proof - (**not shown*)
(*<*)
{
  fix w
  {
    fix g
    {
      assume "G\<^sup>A g w"
      hence 1: "\<forall>Y. (\<P> Y w) \<longleftrightarrow> (\<^bold>\<box>(Y g)) w" by simp
      {
        fix Q
        from 1 have 2: "(\<P> Q w) \<longleftrightarrow> (\<^bold>\<box>(Q g)) w" by (rule allE)
        have  "(\<^bold>\<box>(Q g)) w \<longleftrightarrow> (G\<^sup>A \<Rrightarrow> Q) w" (**we need to prove @{text "\<rightarrow>"} and @{text "\<leftarrow>"}*)
        proof
            assume "(\<^bold>\<box>(Q g)) w" (**suppose g is God-like and necessarily has Q*)
            hence 3: "(\<P> Q w)" using 2 by simp (** then Q is positive*)
            
            {
              fix u
              have "(\<P> Q u) \<longrightarrow> (\<forall>x. G\<^sup>A x u \<longrightarrow> (\<^bold>\<box>(Q x)) u)" 
                by auto (**using the definition of God-like*)
              have "(\<P> Q u) \<longrightarrow> (\<forall>x. G\<^sup>A x u \<longrightarrow> ((Q x)) u)" 
                using refl by auto (**and using @{text "\<box>(\<phi> x) \<longrightarrow> \<phi> x"}*)
            }    
            hence "\<forall>z. (\<P> Q z) \<longrightarrow> (\<forall>x. G\<^sup>A x z \<longrightarrow> Q x z)" by (rule allI)
            hence "\<lfloor>\<P> Q \<^bold>\<rightarrow> (\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> Q x)\<rfloor>"
              by auto (**if Q is positive, then whatever is God-like has Q*)
            hence "\<lfloor>\<^bold>\<box>(\<P> Q \<^bold>\<rightarrow> (\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> Q x))\<rfloor>" by (rule NEC) 
            
            hence "\<lfloor>(\<^bold>\<box>(\<P> Q)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> Q x)\<rfloor>" using K by auto
            hence "\<lfloor>(\<^bold>\<box>(\<P> Q)) \<^bold>\<rightarrow> G\<^sup>A \<Rrightarrow> Q\<rfloor>" by simp
            hence "((\<^bold>\<box>(\<P> Q)) \<^bold>\<rightarrow> G\<^sup>A \<Rrightarrow> Q) w" by (rule allE)
            hence 4: "(\<^bold>\<box>(\<P> Q)) w \<longrightarrow> (G\<^sup>A \<Rrightarrow> Q) w" by simp (*if a property is necessarily positive, then it is entailed by being God-like*)
            have "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" by (rule A4a) (** using axiom 4*)
            hence "(\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> (\<^bold>\<box>(\<P> X))) w" by (rule allE)
            hence "\<P> Q w \<longrightarrow> (\<^bold>\<box>(\<P> Q)) w" by (rule allE)
            hence "\<P> Q w \<longrightarrow> (G\<^sup>A \<Rrightarrow> Q) w" using 4 by simp (*if Q is positive, then it is entailed by being God-like*)
            thus "(G\<^sup>A \<Rrightarrow> Q) w" using 3 by (rule mp) (**@{text "\<rightarrow>"} direction*)
         next
           assume 5: "(G\<^sup>A \<Rrightarrow> Q) w" (**suppose Q is entailed by being God-like*)
           have "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" by (rule A2)
           hence "(\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y) w" by (rule allE)
           hence "\<forall>X Y. (\<P> X w \<and> (X \<Rrightarrow> Y) w) \<longrightarrow> \<P> Y w" by simp
           hence "\<forall>Y. (\<P> G\<^sup>A w \<and> (G\<^sup>A \<Rrightarrow> Y) w) \<longrightarrow> \<P> Y w" by (rule allE)
           hence 6: "(\<P> G\<^sup>A w \<and> (G\<^sup>A \<Rrightarrow> Q) w) \<longrightarrow> \<P> Q w" by (rule allE)
           have "\<lfloor>\<P> G\<^sup>A\<rfloor>" by (rule T2)
           hence "\<P> G\<^sup>A w" by (rule allE)
           hence "\<P> G\<^sup>A w \<and> (G\<^sup>A \<Rrightarrow> Q) w" using 5 by (rule conjI)
           from 6 this have "\<P> Q w" by (rule mp) (**Q is positive by A2 and T2*)
           thus "(\<^bold>\<box>(Q g)) w" using 2 by simp (*@{text "\<leftarrow>"} direction *)
         qed    
     } 
     hence  "\<forall>Z. (\<^bold>\<box>(Z g)) w \<longleftrightarrow> (G\<^sup>A \<Rrightarrow> Z) w" by (rule allI)
     hence "(\<^bold>\<forall>Z. \<^bold>\<box>(Z g) \<^bold>\<leftrightarrow>  G\<^sup>A \<Rrightarrow> Z) w" by simp
     hence "\<E>\<^sup>A G\<^sup>A g w" by simp
    }
    hence "G\<^sup>A g w  \<longrightarrow> \<E>\<^sup>A G\<^sup>A g w " by (rule impI)
  }
  hence "\<forall>x. G\<^sup>A x w  \<longrightarrow> \<E>\<^sup>A G\<^sup>A x w "  by (rule allI)
}
 thus ?thesis by (rule allI) 
qed
theorem GodExistenceImpliesNecExistence: "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" proof -
{
  fix w 
  {
    assume "\<exists>x. G\<^sup>A x w"
    then obtain g where 1: "G\<^sup>A g w" ..
    hence "NE\<^sup>A g w" using A5 by blast                  (* axiom 11.25*)
    hence "\<forall>Y. (\<E>\<^sup>A Y g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w" by simp
    hence 2: "(\<E>\<^sup>A G\<^sup>A g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule allE)
    have  "(\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)) w" using GodIsEssential
      by (rule allE) (* GodIsEssential follows from Axioms 11.11 and 11.3B *)
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
  
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp
(*>*)
(** The necessary existence of God follows from its possible existence:*)    
theorem T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" proof - (**not shown*)
(*<*)      
  have "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using GodExistenceImpliesNecExistence 
    by simp (** follows from Axioms 11.11, 11.25 and 11.3B*)
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using symm tran by metis
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by simp
  hence "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (rule modal_trans)
  thus ?thesis by (rule localImpGlobalCons)
qed
(*>*)
(**The conclusion of the argument can be proven (and with one fewer axiom, though more complex definitions).
\emph{Nitpick} is able to find a countermodel for the \emph{modal collapse}, thus confirming Anderson's (and Fitting's) claims.*)  
lemma GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T3 T4 by metis
lemma ModalCollapse: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick oops (**countersatisfiable*)
    
section \<open>Conclusion\<close>
(** We presented a shallow semantical embedding in Isabelle/HOL for an intensional higher-order modal logic
(a successor of Montague/Gallin intensional logics) as introduced by M. Fitting in his textbook \emph{Types, Tableaus and 
G\"odel's God} @{cite "Fitting,J35"}. 
We employed this logic to formalize and verify all results relevant to the subsequent discussion of three different
variants of the ontological argument: the first one by G\"odel himself (respectively, Scott), the second 
one by Fitting and the last one by Anderson.*)
  
(**By employing an interactive theorem-prover like Isabelle, we were not only able to verify Fitting's results,
but also to guarantee consistency. We could prove even stronger versions
of many of the theorems and find better countermodels (i.e. with smaller cardinality) than the ones presented in his book.
Another interesting aspect was the possibility to explore the implications of alternative formalizations
for definitions and theorems which shed light on interesting philosophical issues concerning entailment,
essentialism and free will, which are currently the subject of some follow-up analysis.*)

(**The latest developments in \emph{automated theorem proving} allow us to engage in much more experimentation
during the formalization and assessment of arguments than ever before. The potential reduction (of several orders of magnitude)
in the time needed for proving or disproving theorems (compared to pen-and-paper proofs), results in almost real-time
feedback about the suitability of our speculations. The practical benefits of computer-supported argumentation go beyond
mere quantitative (easier, faster and more reliable proofs). The advantages are also qualitative, since it fosters a
different approach to argumentation: We can now work iteratively (by trial-and-error) on an argument
by making gradual adjustments to its definitions, axioms and theorems (and getting instant feedback).
This allows us to continuously expose and revise the assumptions we indirectly commit ourselves
everytime we opt for some particular formalization.
*)
(*<*)
end
(*>*)