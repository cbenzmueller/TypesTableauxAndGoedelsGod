(*<*)
theory IHOML
imports Relations
begin  
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
(*>*)
  
section \<open>Introduction\<close>

(** We present a study on Computational Metaphysics: a computer-formalisation and verification
of Fitting's variant of the ontological argument (for the existence of God) as presented in
his textbook \emph{Types, Tableaus and G\"odel's God} @{cite "Fitting"}. Fitting's argument 
is an emendation of Kurt G\"odel's modern variant @{cite "GoedelNotes"} (resp. Dana Scott's 
variant @{cite "ScottNotes"}) of the ontological argument.*)

(**The motivation is to avoid the \emph{modal collapse} @{cite "Sobel,sobel2004logic"}, which has been criticised
as an undesirable side-effect of the axioms of G\"odel resp. Scott. The modal collapse essentially  
states that  there are no contingent truths and that everything is determined.
Several authors (e.g. @{cite "anderson90:_some_emend_of_goedel_ontol_proof,AndersonGettings,Hajek2002,bjordal99"}) 
have proposed emendations of the argument with the aim of maintaining the essential result 
(the necessary existence of God) while at the same time avoiding the modal collapse. 
Related work  has formalised several of these variants on the computer and verified or falsified them. For example,
G\"odel's axioms @{cite "GoedelNotes"} have been shown inconsistent @{cite "C55,C60"}
while Scott's version has been verified @{cite "ECAI"}. Further experiments, contributing amongst others
to the clarification of a related debate between H\'ajek and Anderson, are presented and discussed in
@{cite "J23"}. The enabling technique in all of these experiments has been
shallow semantical embeddings of (extensional) higher-order modal logics in classical higher-order
logic (see @{cite "J23,R59"} and the references therein).*)

(**Fitting's emendation also intends to avoid the modal collapse. However, in contrast to the above variants, Fitting's
solution is based on the use of an intensional as opposed to an extensional higher-order modal logic.
For our work this imposed the additional challenge to provide a shallow embedding of this more advanced
logic. The experiments presented below confirm that Fitting's argument as presented in his textbook @{cite "Fitting"}
is valid and that it avoids the modal collapse as intended.*)

(**The work presented here originates from the \emph{Computational Metaphysics} lecture course  
held at FU Berlin in Summer 2016 @{cite "C65"}. \pagebreak*)


section \<open>Embedding of Intensional Higher-Order Modal Logic\<close>
  
(** The object logic being embedded, intensional higher-order modal logic (IHOML), is a modification of the intentional logic developed by Montague
and Gallin @{cite "Gallin75"}. IHOML is introduced by Fitting in the second part of his textbook @{cite "Fitting"}
in order to formalise his emendation of G\"odel's ontological argument. We offer here a shallow embedding
of this logic in Isabelle/HOL, which has been inspired by previous work on the semantical embedding of
multimodal logics with quantification @{cite "J23"}. We expand this approach to allow for actualist quantifiers,
intensional types and their related operations.*)

subsection \<open>Type Declarations\<close>
  
(** Since IHOML and Isabelle/HOL are both typed languages, we introduce a type-mapping between them.
We follow as closely as possible the syntax given by Fitting (see p. 86).*)

  typedecl i                    (**type for possible worlds *)
  type_synonym io = "(i\<Rightarrow>bool)" (**formulas with world-dependent truth-value*)
  typedecl e  ("\<zero>")             (**individuals *)             
  
  (** Aliases for common unary predicate types: *)
  type_synonym ie =     "(i\<Rightarrow>\<zero>)"             ("\<up>\<zero>")
  type_synonym se =     "(\<zero>\<Rightarrow>bool)"          ("\<langle>\<zero>\<rangle>")
  type_synonym ise =    "(\<zero>\<Rightarrow>io)"           ("\<up>\<langle>\<zero>\<rangle>")
  type_synonym sie =    "(\<up>\<zero>\<Rightarrow>bool)"        ("\<langle>\<up>\<zero>\<rangle>")
  type_synonym isie =   "(\<up>\<zero>\<Rightarrow>io)"         ("\<up>\<langle>\<up>\<zero>\<rangle>")  
  type_synonym sise =   "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>bool)"     ("\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym isise =  "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym sisise=  "(\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
  type_synonym isisise= "(\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>io)"  ("\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
  type_synonym sse =    "\<langle>\<zero>\<rangle>\<Rightarrow>bool"         ("\<langle>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym isse =   "\<langle>\<zero>\<rangle>\<Rightarrow>io"          ("\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>")
  
  (** Aliases for common binary relation types: *)
  type_synonym see =        "(\<zero>\<Rightarrow>\<zero>\<Rightarrow>bool)"          ("\<langle>\<zero>,\<zero>\<rangle>")
  type_synonym isee =       "(\<zero>\<Rightarrow>\<zero>\<Rightarrow>io)"           ("\<up>\<langle>\<zero>,\<zero>\<rangle>")
  type_synonym sieie =      "(\<up>\<zero>\<Rightarrow>\<up>\<zero>\<Rightarrow>bool)"       ("\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>")
  type_synonym isieie =     "(\<up>\<zero>\<Rightarrow>\<up>\<zero>\<Rightarrow>io)"        ("\<up>\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>")
  type_synonym ssese =      "(\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>\<Rightarrow>bool)"     ("\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym issese =     "(\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym ssee =       "(\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>bool)"       ("\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
  type_synonym issee =      "(\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>io)"        ("\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
  type_synonym isisee =     "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>io)"      ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
  type_synonym isiseise =   "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>\<Rightarrow>io)"    ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym isiseisise=  "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
  
subsection \<open>Definitions\<close>
  
subsubsection \<open>Logical Operators as Truth-Sets\<close>    

  abbreviation mnot   :: "io\<Rightarrow>io" ("\<^bold>\<not>_"[52]53)
    where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  abbreviation negpred :: "\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>" ("\<rightharpoondown>_"[52]53) 
    where "\<rightharpoondown>\<Phi> \<equiv> \<lambda>x. \<not>(\<Phi> x)" 
  abbreviation mnegpred :: "\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("\<^bold>\<rightharpoondown>_"[52]53) 
    where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>(\<Phi> x w)"
  abbreviation mand   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<and>"51)
    where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"   
  abbreviation mor    :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<or>"50)
    where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
  abbreviation mimp   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<rightarrow>"49) 
    where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"  
  abbreviation mequ   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<leftrightarrow>"48)
    where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
  abbreviation xor:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr"\<oplus>"50)
    where "\<phi>\<oplus>\<psi> \<equiv>  (\<phi>\<or>\<psi>) \<and> \<not>(\<phi>\<and>\<psi>)" 
  abbreviation mxor   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<oplus>"50)
    where "\<phi>\<^bold>\<oplus>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<oplus>(\<psi> w)"
      
subsubsection \<open>Possibilist Quantification\<close>
    
  abbreviation mforall   :: "('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<forall>")      
    where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mexists   :: "('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<exists>") 
    where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"
    
  abbreviation mforallB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<forall>"[8]9) (**Binder notation*)
    where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexistsB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<exists>"[8]9)
    where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 
      
subsubsection \<open>Actualist Quantification\<close>
  
(** The following predicate is used to model actualist quantifiers by restricting the domain of quantification at every possible world.
This standard technique has been referred to as \emph{existence relativization} (@{cite "fitting98"}, p. 106),
highlighting the fact that this predicate can be seen as a kind of meta-logical `existence predicate' telling us
which individuals \emph{actually} exist at a given world. This meta-logical concept does not appear in our object language.*)
  consts Exists::"\<up>\<langle>\<zero>\<rangle>" ("existsAt")  

  abbreviation mforallAct   :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<^bold>\<forall>\<^sup>E")    
    where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x. (existsAt x w)\<longrightarrow>(\<Phi> x w)"
  abbreviation mexistsAct   :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<^bold>\<exists>\<^sup>E") 
    where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. (existsAt x w) \<and> (\<Phi> x w)"

  abbreviation mforallActB  :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" (binder"\<^bold>\<forall>\<^sup>E"[8]9) (**binder notation*)
    where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
  abbreviation mexistsActB  :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" (binder"\<^bold>\<exists>\<^sup>E"[8]9)
    where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"
      
subsubsection \<open>Modal Operators\<close>
  
   consts aRel::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)  (** accessibility relation \emph{r} *)
  
  abbreviation mbox   :: "io\<Rightarrow>io" ("\<^bold>\<box>_"[52]53)
    where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
  abbreviation mdia   :: "io\<Rightarrow>io" ("\<^bold>\<diamond>_"[52]53)
    where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"

subsubsection \<open>\emph{Extension-of} Operator\<close>
(** The IHOML operator @{text "\<down>"} is embedded as a predicate applying to (world-dependent) atomic formulas
 whose first argument is a \emph{relativized term} (i.e. a non-rigid term). This approach slightly differs from  
 the one taken in Fitting's book, where @{text "\<down>"} is an operator which, when applied to a (rigid) intensional term,
 gives us a new (non-rigid) extensional term (see @{cite "Fitting"}, p. 93, for more details). Also note that,
 depending on the particular types involved, we had to define this operator differently (\emph{a-d} below) to ensure 
 type correctness.
 Nevertheless, in both approaches the essence of the \emph{Extension-of} operator remains the same:
 a term of the form @{text "\<down>\<phi>"} behaves as a non-rigid term, whose denotation at a given possible world corresponds
 to the extension of the original intensional term @{text "\<phi>"} at that world.*)

(** (\emph{a}) Predicate @{text \<phi>} takes an (intensional) individual concept as argument:*)
abbreviation mextIndiv::"\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<zero>\<Rightarrow>io" (infix "\<^bold>\<downharpoonleft>" 60)                             
  where "\<phi> \<^bold>\<downharpoonleft>c \<equiv> \<lambda>w. \<phi> (c w) w"
(** (\emph{b}) Predicate @{text \<phi>} takes an intensional predicate as argument:*)
abbreviation mextPredArg::"(('t\<Rightarrow>io)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<^bold>\<down>" 60)
  where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x u. P x w) w"
(** (\emph{c}) Predicate @{text \<phi>} takes an extensional predicate as argument:*)
abbreviation extPredArg::"(('t\<Rightarrow>bool)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<down>" 60)
  where "\<phi> \<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. P x w) w"
(** (\emph{d}) Predicate @{text \<phi>} takes an extensional predicate as \emph{first} argument:*)
abbreviation extPredArg1::"(('t\<Rightarrow>bool)\<Rightarrow>'b\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>'b\<Rightarrow>io" (infix "\<down>\<^sub>1" 60)
  where "\<phi> \<down>\<^sub>1P \<equiv> \<lambda>z. \<lambda>w. \<phi> (\<lambda>x. P x w) z w"
 (**\bigbreak*)   
subsubsection \<open>Equality\<close>
  
  abbreviation meq    :: "'t\<Rightarrow>'t\<Rightarrow>io" (infix"\<^bold>\<approx>"60) (**normal equality (for all types)*)
    where "x \<^bold>\<approx> y \<equiv> \<lambda>w. x = y"
  abbreviation meqC   :: "\<up>\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>" (infixr"\<^bold>\<approx>\<^sup>C"52) (**eq. for individual concepts*)
    where "x \<^bold>\<approx>\<^sup>C y \<equiv> \<lambda>w. \<forall>v. (x v) = (y v)"
  abbreviation meqL   :: "\<up>\<langle>\<zero>,\<zero>\<rangle>" (infixr"\<^bold>\<approx>\<^sup>L"52) (**Leibniz eq. for individuals*)
    where "x \<^bold>\<approx>\<^sup>L y \<equiv> \<^bold>\<forall>\<phi>. \<phi>(x)\<^bold>\<rightarrow>\<phi>(y)"

subsubsection \<open>Meta-logical Predicates\<close>

 abbreviation valid :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>" [8]) where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)"
 abbreviation satisfiable :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>s\<^sup>a\<^sup>t" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<equiv> \<exists>w.(\<psi> w)"
 abbreviation countersat :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  \<exists>w.\<not>(\<psi> w)"
 abbreviation invalid :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>i\<^sup>n\<^sup>v" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>i\<^sup>n\<^sup>v \<equiv> \<forall>w.\<not>(\<psi> w)"

subsection \<open>Verifying the Embedding\<close>
   
(** The above definitions introduce modal logic \emph{K} with possibilist and actualist quantifiers,
as evidenced by the following tests:*)

 (** Verifying \emph{K} Principle and Necessitation: *)
 lemma K: "\<lfloor>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>" by simp    (** \emph{K} schema *)
 lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" by simp    (** necessitation *)
    
 (** Local consequence implies global consequence (we will use this lemma often):*)
 lemma localImpGlobalCons: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor>" by simp
    
 (** But global consequence does not imply local consequence:*)
 lemma "\<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor>" nitpick oops (** countersatisfiable*)

 (** Barcan and Converse Barcan Formulas are satisfied for standard (possibilist) quantifiers: *)
 lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))\<rfloor>" by simp
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp
    
 (** (Converse) Barcan Formulas not satisfied for actualist quantifiers: *)
 lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops (** countersatisfiable*)
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops (** countersatisfiable*)
    
(** Above we have made use of (counter-)model finder \emph{Nitpick} @{cite "Nitpick"} for the first time.  
For all the conjectured lemmas above, \emph{Nitpick} has found a countermodel, i.e. a model satisfying all 
the axioms which falsifies the given formula. This means, the formulas are not valid.*)   
 
 (** Well known relations between meta-logical notions: *)
 lemma  "\<lfloor>\<phi>\<rfloor> \<longleftrightarrow> \<not>\<lfloor>\<phi>\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t" by simp
 lemma  "\<lfloor>\<phi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not>\<lfloor>\<phi>\<rfloor>\<^sup>i\<^sup>n\<^sup>v " by simp
 
 (** Contingent truth does not allow for necessitation: *)
 lemma "\<lfloor>\<^bold>\<diamond>\<phi>\<rfloor>  \<longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" nitpick oops            (** countersatisfiable*)
 lemma "\<lfloor>\<^bold>\<box>\<phi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" nitpick oops           (** countersatisfiable*)

 (** \emph{Modal collapse} is countersatisfiable: *)
 lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick oops                  (** countersatisfiable*)

subsection \<open>Useful Definitions for Axiomatization of Further Logics\<close>

 (** The best known normal logics (\emph{K4, K5, KB, K45, KB5, D, D4, D5, D45, ...}) can be obtained by
 combinations of the following axioms: *)

  abbreviation M 
    where "M \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
  abbreviation B 
    where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  abbreviation D 
    where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
  abbreviation IV 
    where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
  abbreviation V 
    where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  
  (** Instead of postulating (combinations of) the above  axioms we instead make use of 
  the well-known \emph{Sahlqvist correspondence}, which links axioms to constraints on a model's accessibility
  relation (e.g. reflexive, symmetric, etc.; the definitions of which are not shown here). We show
  that  reflexivity, symmetry, seriality, transitivity and euclideanness imply
  axioms $M, B, D, IV, V$ respectively.*)

  lemma "reflexive aRel  \<Longrightarrow>  \<lfloor>M\<rfloor>" by blast (** aka T *)
  lemma "symmetric aRel \<Longrightarrow> \<lfloor>B\<rfloor>" by blast
  lemma "serial aRel  \<Longrightarrow> \<lfloor>D\<rfloor>" by blast         
  lemma "transitive aRel  \<Longrightarrow> \<lfloor>IV\<rfloor>" by blast   
  lemma "euclidean aRel \<Longrightarrow> \<lfloor>V\<rfloor>" by blast         
  lemma "preorder aRel \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>IV\<rfloor>" by blast (** S4: reflexive + transitive*)
  lemma "equivalence aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (** S5: preorder + symmetric *)
  lemma "reflexive aRel \<and> euclidean aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (** S5 *)

  (** Using these definitions, we can derive axioms for the most common modal logics (see also @{cite "C47"}). 
  Thereby we are free to use either the semantic constraints or the related \emph{Sahlqvist} axioms. Here we provide 
  both versions. In what follows we use the semantic constraints (for improved performance).
  \pagebreak*)
 
(*<*)      
end
(*>*)      