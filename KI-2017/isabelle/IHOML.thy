(*<*)
theory IHOML
imports Relations
begin  
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
(*>*)
  
(**
\begin{abstract}
	A computer-formalization in Isabelle/HOL of several variants of G\"odel's ontological argument is presented
	(as discussed in M. Fitting's textbook \emph{Types, Tableaus and G\"odel's God}). Fitting's work
	introduces an intensional higher-order modal logic (by drawing on Montague/Gallin approach), which we
	shallowly embed here in classical higher-order logic (Isabelle/HOL). We then	utilize the embedded logic for the
  formalization of the ontological argument. In particular, Fitting's and Anderson's variants are verified
  and their claims confirmed. These variants aim to avoid the modal collapse, which has been criticized as
  an undesirable side-effect of Kurt G\"odel's (and Dana Scott's) versions of the ontological argument.
  \\ \\
  \textbf{Keywords:} Automated Theorem Proving. Computational Metaphysics. Isabelle. Modal Logic.
	Intensional Logic. Ontological Argument
\end{abstract}
*)
  
(*- old version
	A computer-formalization of the essential parts of Fitting's textbook
	\emph{Types, Tableaus and G\"odel's Go}d in Isabelle/HOL is
	presented. In particular, Fitting's (and Anderson's) variant of the ontological
	argument is verified and confirmed. This variant avoids the modal
	collapse, which has been criticized as an undesirable side-effect of Kurt G\"odel's (and
	Dana Scott's) versions of the ontological argument. Fitting's work
	is employing an intensional higher-order modal logic, which we
	shallowly embed here in classical higher-order logic. We then
	utilize the embedded logic for the formalization of Fitting's argument.
*)  
  
section \<open>Introduction\<close>
(** We present a shallow semantical embedding of an \emph{intensional} higher-order modal logic (IHOML) in Isabelle/HOL
which has been introduced Fitting in his textbook \emph{Types, Tableaus and G\"odel's God} @{cite "Fitting"} in order
to formalize his emendation of G\"odel's ontological argument (for the existence of God). IHOML is a modification of the
intentional logic originally developed by Montague and later expanded by Gallin @{cite "Gallin75"} by building upon Church's
type theory and Kripke's possible-world semantics. Our approach has been inspired by previous work on the semantical embedding of
multimodal logics with quantification @{cite "J23"}, which we expand here to allow for actualist quantification,
intensional terms and their related operations.*)
  
(** We subsequently present a study on Computational Metaphysics: a computer-formalization and verification
of G\"odel's @{cite "GoedelNotes"} (resp. Dana Scott's @{cite "ScottNotes"}) modern variant of the ontological argument,
followed by Fitting's emendation thereof. A third variant (by Anderson @{cite "anderson90:_some_emend_of_goedel_ontol_proof"})
is also discussed. The motivation is to avoid the \emph{modal collapse} @{cite "Sobel,sobel2004logic"}, which has been criticized
as an undesirable side-effect of the axioms of G\"odel (resp. Scott). The modal collapse essentially  
states that there are no contingent truths and that everything is determined.
Several authors (e.g. @{cite "anderson90:_some_emend_of_goedel_ontol_proof,AndersonGettings,Hajek2002,bjordal99"}) 
have proposed emendations of the argument with the aim of maintaining the essential result 
(the necessary existence of God) while at the same time avoiding the modal collapse. 
Related work  has formalized several of these variants on the computer and verified or falsified them. For example,
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
is valid and that it avoids the modal collapse as intended. The work presented here originates from 
the \emph{Computational Metaphysics} lecture course held at FU Berlin in Summer 2016 @{cite "C65"}.*)


section \<open>Embedding of Intensional Higher-Order Modal Logic\<close>

subsection \<open>Type Declarations\<close>  
(** Since IHOML and Isabelle/HOL are both typed languages, we introduce a type-mapping between them.
We follow as closely as possible the syntax given by Fitting (see p. 86). According to this syntax,
if @{text "\<tau>"} is an extensional type, @{text "\<up>\<tau>"} is the corresponding intensional type. For instance,
a set of (red) objects has the extensional type @{text "\<langle>\<zero>\<rangle>"}, whereas the concept `red' has intensional type @{text "\<up>\<langle>\<zero>\<rangle>"}.*)

typedecl i                    (**type for possible worlds *)
type_synonym io = "(i\<Rightarrow>bool)" (**formulas with world-dependent truth-value*)
typedecl e  ("\<zero>")             (**individual objects *)             

(** Aliases for common complex types (predicates and relations):*)
type_synonym ie="(i\<Rightarrow>\<zero>)" ("\<up>\<zero>") (**individual concepts map worlds to objects*)
type_synonym se="(\<zero>\<Rightarrow>bool)" ("\<langle>\<zero>\<rangle>") (** (extensional) sets*)
type_synonym ise="(\<zero>\<Rightarrow>io)" ("\<up>\<langle>\<zero>\<rangle>") (** intensional (predicate) concepts*) 
type_synonym sise="(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>") (** sets of concepts*) 
type_synonym isise="(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>") (** 2nd-order intensional concepts*) 
(*<*)
type_synonym sie=     "(\<up>\<zero>\<Rightarrow>bool)" ("\<langle>\<up>\<zero>\<rangle>")
type_synonym isie=    "(\<up>\<zero>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<zero>\<rangle>")
type_synonym sisise=  "(\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
type_synonym isisise= "(\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>io)"  ("\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
type_synonym sse =    "\<langle>\<zero>\<rangle>\<Rightarrow>bool"         ("\<langle>\<langle>\<zero>\<rangle>\<rangle>")
type_synonym isse =   "\<langle>\<zero>\<rangle>\<Rightarrow>io"          ("\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>") 
(*>*)
type_synonym see="(\<zero>\<Rightarrow>\<zero>\<Rightarrow>bool)" ("\<langle>\<zero>,\<zero>\<rangle>") (**(extensional) relations*)
type_synonym isee="(\<zero>\<Rightarrow>\<zero>\<Rightarrow>io)" ("\<up>\<langle>\<zero>,\<zero>\<rangle>") (**intensional relational concepts*)
type_synonym isisee="(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>") (**2nd-order intensional relation*) 
(*<*)  
type_synonym sieie="(\<up>\<zero>\<Rightarrow>\<up>\<zero>\<Rightarrow>bool)"       ("\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>")
type_synonym isieie =     "(\<up>\<zero>\<Rightarrow>\<up>\<zero>\<Rightarrow>io)"        ("\<up>\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>")
type_synonym ssese =      "(\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>\<Rightarrow>bool)"     ("\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>")
type_synonym issese =     "(\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>")
type_synonym ssee =       "(\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>bool)"       ("\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
type_synonym issee =      "(\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>io)"        ("\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
type_synonym isiseise =   "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>\<Rightarrow>io)"    ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>")
type_synonym isiseisise=  "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
(*>*) 
subsection \<open>Logical Constants as Truth-Sets\<close>    
(**We embed each modal operator as the set of worlds satisfying the corresponding HOL formula.*)
  
  abbreviation mnot   :: "io\<Rightarrow>io" ("\<^bold>\<not>_"[52]53)
    where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  abbreviation mand   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<and>"51)
    where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"   
  abbreviation mor    :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<or>"50)
    where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
  abbreviation mimp   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<rightarrow>"49) 
    where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)" 
(*<*)
  abbreviation mequ   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<leftrightarrow>"48)
    where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
  abbreviation xor:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr"\<oplus>"50)
    where "\<phi>\<oplus>\<psi> \<equiv>  (\<phi>\<or>\<psi>) \<and> \<not>(\<phi>\<and>\<psi>)" 
  abbreviation mxor   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<oplus>"50)
    where "\<phi>\<^bold>\<oplus>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<oplus>(\<psi> w)"
  abbreviation negpred :: "\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>" ("\<rightharpoondown>_"[52]53) 
    where "\<rightharpoondown>\<Phi> \<equiv> \<lambda>x. \<not>(\<Phi> x)" 
  abbreviation mnegpred :: "\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("\<^bold>\<rightharpoondown>_"[52]53) 
    where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>(\<Phi> x w)"
(*>*)      
(**Following can be seen as modelling \emph{possibilist quantification}:*)    
  abbreviation mforall::"('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mexists::"('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"    
(*<*)
  abbreviation mforallB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<forall>"[8]9) (**Binder notation*)
    where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexistsB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<exists>"[8]9)
    where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 
(*>*)      
(** The \emph{existsAt} predicate is used to embed actualist quantifiers by restricting the domain of quantification at every possible world.
This standard technique has been referred to as \emph{existence relativization} (@{cite "fitting98"}, p. 106),
highlighting the fact that this predicate can be seen as a kind of meta-logical `existence predicate' telling us
which individuals \emph{actually} exist at a given world. This meta-logical concept does not appear in our object language.*)
  consts ExistsAt::"\<up>\<langle>\<zero>\<rangle>" (infix "existsAt" 70)  

  abbreviation mforallAct::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<^bold>\<forall>\<^sup>E") (**actualist variants use superscript!*)
    where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x. (x existsAt w)\<longrightarrow>(\<Phi> x w)"
  abbreviation mexistsAct::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<^bold>\<exists>\<^sup>E")
    where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. (x existsAt w) \<and> (\<Phi> x w)"
(*<*)
  abbreviation mforallActB::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" (binder"\<^bold>\<forall>\<^sup>E"[8]9) (**binder notation*)
    where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
  abbreviation mexistsActB::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" (binder"\<^bold>\<exists>\<^sup>E"[8]9)
    where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"
(*>*)      
(**\emph{aRel} is the frame's \emph{accessibility relation} (aliased \emph{r}) used to embed the modal operators
@{text "\<box>"} and @{text "\<diamond>"}.*)  
  consts aRel::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)
  abbreviation mbox :: "io\<Rightarrow>io" ("\<^bold>\<box>_"[52]53) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
  abbreviation mdia :: "io\<Rightarrow>io" ("\<^bold>\<diamond>_"[52]53) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"
      
subsection \<open>\emph{Extension-of} Operator\<close> 
(**According to Fitting's semantics (@{cite "Fitting"}, pp. 92-4) @{text "\<down>"} is an unary operator applying only to 
 intensional terms. A term of the form @{text "\<down>\<alpha>"} designates the extension of the intensional object designated by 
 @{text "\<alpha>"}, at some \emph{given} world. For instance, suppose we take possible worlds as persons,
 we can therefore think of the concept `red' as a function that maps each person to the set of objects that person
 classifies as red (its extension). We can further state, the intensional term \emph{r} of type @{text "\<up>\<langle>\<zero>\<rangle>"} designates the concept `red'.
 As can be seen, intensional terms in IHOML designate functions on possible worlds and they always do it \emph{rigidly}. 
 We will sometimes refer to an intensional object explicitly as `rigid', implying that its (rigidly) designated function has
 the same extension in all possible worlds. (The notion of rigidity was introduced by Kripke in @{cite "kripke1980"},
 where he discusses its interesting philosophical ramifications at some length.)*)

(** Terms of the form @{text "\<down>\<alpha>"} are called \emph{relativized} (extensional) terms; they are always derived
from intensional terms and their type is \emph{extensional} (in the color example @{text "\<down>r"} would be of type @{text "\<langle>\<zero>\<rangle>"}).
Relativized terms may vary their denotation from world to world of a model, because the extension of an intensional term can change
from world to world, i.e. they are non-rigid.*)
(**To recap: an intensional term denotes the same function in all worlds (i.e. it's rigid), whereas a relativized term
denotes a (possibly) different extension (an object or a set) at every world (i.e. it's non-rigid). To find out
the denotation of a relativized term, a world must be given. Relativized terms are the \emph{only} non-rigid terms.*)
(** For our Isabelle/HOL embedding, we had to follow a slightly different approach; we model @{text "\<down>"}
as a predicate applying to formulas of the form @{text "\<Phi>(\<down>\<alpha>\<^sub>1,\<dots>\<alpha>\<^sub>n)"} (for our treatment
we only need to consider cases involving one or two arguments, the first one being a relativized term).
For instance, the formula @{text "Q(\<down>a\<^sub>1)\<^sup>w"} (evaluated at world \emph{w}) is modelled as @{text "\<downharpoonleft>(Q,a\<^sub>1)\<^sup>w"}
(or @{text "(Q \<downharpoonleft> a\<^sub>1)\<^sup>w"} using infix notation), which gets further translated into @{text "Q(a\<^sub>1(w))\<^sup>w"}.*)
  
(*Depending on the particular types involved, we have to define @{text "\<down>"} differently to ensure type correctness
(see \emph{a-d} below). Nevertheless, the essence of the \emph{Extension-of} operator remains the same:
a term @{text "\<alpha>"} preceded by @{text "\<down>"} behaves as a non-rigid term, whose denotation at a given possible world corresponds
to the extension of the original intensional term @{text "\<alpha>"} at that world.*)

(** (\emph{a}) Predicate @{text \<phi>} takes as argument a relativized term derived from an (intensional) individual of type @{text "\<up>\<zero>"}:*)
abbreviation extIndivArg::"\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<zero>\<Rightarrow>io" (infix "\<downharpoonleft>" 60)                           
  where "\<phi> \<downharpoonleft>c \<equiv> \<lambda>w. \<phi> (c w) w"
(** (\emph{b}) A variant of (\emph{a}) for terms derived from predicates (types of form @{text "\<up>\<langle>t\<rangle>"}):*)
abbreviation extPredArg::"(('t\<Rightarrow>bool)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<down>" 60)
  where "\<phi> \<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. P x w) w"
(*<*)    
(** (\emph{c}) A variant of (\emph{b}) with a second argument (the first one being relativized):*)
abbreviation extPredArg1::"(('t\<Rightarrow>bool)\<Rightarrow>'b\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>'b\<Rightarrow>io" (infix "\<down>\<^sub>1" 60)
  where "\<phi> \<down>\<^sub>1P \<equiv> \<lambda>z. \<lambda>w. \<phi> (\<lambda>x. P x w) z w"
    
(**In what follows, the `@{text "\<lparr>_\<rparr>"}' parentheses are an operator used to convert extensional objects into `rigid' intensional ones:*)  
abbreviation trivialConversion::"bool\<Rightarrow>io" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> (\<lambda>w. \<phi>)"  
(** (\emph{d}) A variant of (\emph{b}) where @{text \<phi>} takes `rigid' intensional terms as argument:*)
abbreviation mextPredArg::"(('t\<Rightarrow>io)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<^bold>\<down>" 60)
  where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. \<lparr>P x w\<rparr>) w" (* where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x u. P x w) w"*)
(*>*)    
subsection \<open>Equality\<close>
  
  abbreviation meq    :: "'t\<Rightarrow>'t\<Rightarrow>io" (infix"\<^bold>\<approx>"60) (**normal equality (for all types)*)
    where "x \<^bold>\<approx> y \<equiv> \<lambda>w. x = y"
  abbreviation meqC   :: "\<up>\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>" (infixr"\<^bold>\<approx>\<^sup>C"52) (**eq. for individual concepts*)
    where "x \<^bold>\<approx>\<^sup>C y \<equiv> \<lambda>w. \<forall>v. (x v) = (y v)"
  abbreviation meqL   :: "\<up>\<langle>\<zero>,\<zero>\<rangle>" (infixr"\<^bold>\<approx>\<^sup>L"52) (**Leibniz eq. for individuals*)
    where "x \<^bold>\<approx>\<^sup>L y \<equiv> \<^bold>\<forall>\<phi>. \<phi>(x)\<^bold>\<rightarrow>\<phi>(y)"
 
subsection \<open>Verifying the Embedding\<close>
 (** The above definitions introduce modal logic \emph{K} with possibilist and actualist quantifiers,
as evidenced by the following tests:*)
   
 abbreviation valid::"io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)" (**modal validity *)

 (** Verifying \emph{K} principle and the \emph{necessitation} rule: *)
 lemma K: "\<lfloor>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>" by simp    (** \emph{K} schema *)
 lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" by simp    (** necessitation *)
    
 (** Local consequence implies global consequence (but not the other way round!):*)
 lemma localImpGlobalCons: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor>" by simp
 lemma "\<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor>" nitpick oops (** countersatisfiable*)

 (** (Converse-)Barcan formulas are satisfied for possibilist, but not for actualist, quantifiers:*)
 lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))\<rfloor>" by simp
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp
 lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops (** countersatisfiable*)
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops (** countersatisfiable*)
    
  (** We have made use of (counter-)model finder \emph{Nitpick} @{cite "Nitpick"} for the first time.  
  For all the conjectured lemmas above, \emph{Nitpick} has found a countermodel, i.e. a model satisfying all 
  the axioms which falsifies the given formula. This means, the formulas are not valid.*)
       
  (** @{text "\<beta>\<eta>"}-redex is valid for non-relativized (intensional or extensional) terms: *)
  lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<zero>)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp
  lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp    
  (** @{text "\<beta>\<eta>"}-redex is valid for relativized terms as long as no modal operators occur inside the predicate abstract: *)
  lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<phi> \<downharpoonleft>\<tau>)\<rfloor>" by simp
  lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<downharpoonleft>\<tau>)\<rfloor>" nitpick oops (**countersatisfiable*)
  lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<diamond>\<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<diamond>\<phi> \<downharpoonleft>\<tau>)\<rfloor>" nitpick oops (**countersatisfiable  *)
  
  (** \emph{Modal collapse} is countersatisfiable:*)
  lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick oops   (** countersatisfiable*)

subsection \<open>Useful Definitions for Axiomatization of Further Logics\<close>

(**The best known normal logics (\emph{K4, K5, KB, K45, KB5, D, D4, D5, D45, ...}) can be obtained by
 combinations of the following axioms: *)
  abbreviation M  where "M \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
  abbreviation B  where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  abbreviation D  where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
  abbreviation IV where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
  abbreviation V  where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  
  (** Instead of postulating (combinations of) the above  axioms we instead make use of 
  the well-known \emph{Sahlqvist correspondence}, which links axioms to constraints on a model's accessibility
  relation (e.g. reflexive, symmetric, etc). We show  that  reflexivity, symmetry, seriality, transitivity and euclideanness imply
  axioms $M, B, D, IV, V$ respectively.*)

  lemma "reflexive aRel  \<Longrightarrow>  \<lfloor>M\<rfloor>" by blast (** aka T *)
  lemma "symmetric aRel \<Longrightarrow> \<lfloor>B\<rfloor>" by blast
  lemma "serial aRel  \<Longrightarrow> \<lfloor>D\<rfloor>" by blast         
  lemma "transitive aRel  \<Longrightarrow> \<lfloor>IV\<rfloor>" by blast   
  lemma "euclidean aRel \<Longrightarrow> \<lfloor>V\<rfloor>" by blast         
  lemma "preorder aRel \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>IV\<rfloor>" by blast (**S4: reflexive + transitive*)
  lemma "equivalence aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (**S5: preorder + symmetric*)
  lemma "reflexive aRel \<and> euclidean aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast (** S5 *)

  (** Using these definitions, we can derive axioms for the most common modal logics (see also @{cite "C47"}). 
  Thereby we are free to use either the semantic constraints or the related \emph{Sahlqvist} axioms. Here we provide 
  both versions. In what follows we use the semantic constraints (for improved performance).*)
    
subsection \<open>Textbook Examples\<close>
(** In this section we provide further evidence that our embedded logic works as intended by proving the examples
 discussed in Fitting's textbook @{cite "Fitting"}. We were able to confirm that all results agree with his claims.*)
    
(** Example 7.13, p. 96:*)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>"
  nitpick[card 't=1, card i=2] oops (** nitpick finds same counterexample as book*)
    
(** Example 7.14, p. 98:*)
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
    
(** Example 7.15, p. 99:*)
lemma "\<lfloor>\<^bold>\<box>(P (c::\<up>\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<up>\<zero>. \<^bold>\<box>(P x))\<rfloor>" by auto 

(** Example 7.16, p. 100:*)
lemma "\<lfloor>\<^bold>\<box>(P \<downharpoonleft>(c::\<up>\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<zero>. \<^bold>\<box>(P x))\<rfloor>" 
  nitpick[card 't=2, card i=2] oops (** counterexample with two worlds found *)
    
(** Example 7.17, p. 101:*)
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>\<zero>. (\<lambda>x::\<zero>.  \<^bold>\<box>((\<lambda>y::\<zero>.  x \<^bold>\<approx> y) \<downharpoonleft>Z)) \<downharpoonleft>Z\<rfloor>" 
  nitpick[card 't=2, card i=2] oops (** countersatisfiable *)
lemma "\<lfloor>\<^bold>\<forall>z::\<zero>.  (\<lambda>x::\<zero>.  \<^bold>\<box>((\<lambda>y::\<zero>.  x \<^bold>\<approx> y)  z)) z\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>\<zero>. (\<lambda>X::\<up>\<zero>. \<^bold>\<box>((\<lambda>Y::\<up>\<zero>. X \<^bold>\<approx> Y)  Z)) Z\<rfloor>" by simp

(** Example 9.1, p.116 (using normal-, Leibniz- and concept-equality)*) (* statesman-like president-material*)
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<downharpoonleft>(p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx> x) \<downharpoonleft>p))\<rfloor>" by auto (* using normal equality *)
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<downharpoonleft>(p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>L x) \<downharpoonleft>p))\<rfloor>" by auto (* using Leibniz equality *)
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X  (p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>C x) p))\<rfloor>" by simp (* using equality as defined for individual concepts *)

subsection \<open>Stability Conditions and Rigid Designation\<close>
  
(**As said before, intensional terms are trivially rigid. The following predicate tests whether an intensional
predicate is `rigid' in the sense of denoting a world-independent function.*)   
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
  "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
  
(**Following definitions are called `stability conditions' by Fitting (@{cite "Fitting"}, p. 124).*)
abbreviation stabilityA::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityA \<tau> \<equiv> \<^bold>\<forall>\<alpha>. (\<tau> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<tau> \<alpha>)"
abbreviation stabilityB::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityB \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<diamond>(\<tau> \<alpha>) \<^bold>\<rightarrow> (\<tau> \<alpha>)"

(**We prove them equivalent in \emph{S5} logic (using \emph{Sahlqvist correspondence}).*)  
lemma "equivalence aRel \<Longrightarrow> \<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityB \<tau>\<rfloor>" by blast    
lemma "equivalence aRel \<Longrightarrow> \<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityA \<tau>\<rfloor>" by blast    
    
(** A term is rigid if and only if it satisfies the stability conditions.*)
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longleftrightarrow> \<lfloor>(stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<zero>\<rangle>)\<rfloor> \<longleftrightarrow> \<lfloor>(stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
    
subsection \<open>\emph{De Re} and \emph{De Dicto}\<close>
(** \emph{De re} is equivalent to \emph{de dicto} for non-relativized (i.e. rigid) terms: *)
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<langle>\<zero>\<rangle>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
(** \emph{De re} is not equivalent to \emph{de dicto} for relativized terms: *)    
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>(\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops (** countersatisfiable *)
 
(*<*)      
end
(*>*)      