\documentclass{article}

\usepackage{CoSchemes}

%include CoSchemes.fmt

\begin{document}

%if style == newcode
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances #-}

module CoSchemes where

\end{code}
%endif

\title{Draft: ``matching'' coercion axioms in \FC}

\maketitle

\begin{abstract}
This document presents a rough design for a possible future extension to \FC
to allow a limited form of overlapping type family instances in GHC.
\end{abstract}

\section{The problem}
Type families, especially in the form of associated type synonyms, often appear
closely tied to type classes. However, there are crucial differences between
the two when it comes to overlap. Consider the following class:

\begin{code}
  class C aT bT where c :: aT -> bT -> Bool

  instance C aT aT where c _ _ = True
  instance C aT bT where c _ _ = False
\end{code}
%
With \texttt{-XOverlappingInstances}, the code compiles and works fine. In the
absence of other instances, the function |c| takes two arguments and returns
|True| if those arguments are of the same type, or |False| otherwise.

We could try to encode the same behavior at the type level:
\begin{spec}
  data TrueT
  data FalseT

  type family FT aT bT
  type instance FT aT aT = TrueT
  type instance FT aT bT = FalseT
\end{spec}
However, this code is rejected by GHC, as there are ``conflicting family
instance declarations''. Currently, family instances are only allowed to overlap
if their right-hand side coincides. The reason for this restriction is to
prevent the creation of unsound \FC coercions. If we could write the code
above, it would give rise to the following two coercion axioms:
\begin{spec}
ax1 :: forall aT.     FT aT aT ~ TrueT
ax2 :: forall aT bT.  FT aT bT ~ FalseT
\end{spec}
It is now easy to construct conflicting proofs:
\begin{spec}
ax1 Int      :: FT Int Int ~ TrueT
ax2 Int Int  :: FT Int Int ~ FalseT
\end{spec}
%
We can therefore conclude that the current translation of family instances into
\FC is incompatible with overlapping family instances.

However, the ability to declare overlapping type instances can be very useful.
Ticket \href{http://hackage.haskell.org/trac/ghc/ticket/4259}{\#4259} is an old
feature request for overlapping type instances, with a recent comment pointing
out that associated type defaults (recently implemented) can especially profit
from allowing overlapping. The HList library \cite{HList}, for example, relies
on static determination of type equality. Oleg Kiselyov has investigated how to
replace overlapping instances in the presence of a type-level equality test%
\footnote{\url{http://okmij.org/ftp/Haskell/typeEQ.html}}. We believe that
having some form of overlapping type family instances would allow
simplifying many existing Haskell programs, while at the same time reducing the
disparity between type families and functional dependencies (the latter, being
in type classes, are allowed to overlap).

%if False
The common need for overlapping type instances arises
when defining ``catch-all'' behaviour: we want adhoc instances for some cases,
and a generic case for the rest. For instance, testing whether a datatype has
selectors, at the type level, with the
\href{http://www.haskell.org/haskellwiki/Generics}{generic programming mechanism}
in GHC:
\begin{spec}
type family HasSel (rT :: * -> *)
type instance HasSel (M1 DT cT fT)              = HasSel fT
type instance HasSel (M1 CT cT fT)              = HasSel fT
type instance HasSel (fT :+: gT)                = HasSel fT :||: HasSel gT

type instance HasSel (M1 ST NoSelector fT)      = TrueT
type instance HasSel (M1 ST cT fT)              = FalseT
\end{spec}
Notice the overlap in the final two clauses. Currently we would have to write an
instance for each possible |cT| in |M1 ST cT|. Besides being cumbersome, that 
is also impossible in this particular situation, because |cT| will be
instantiated with internal datatypes generated while deriving the |Generic|
instance.
%endif

\section{What we want to do}
The problem arises from generating a coercion from each type instance. However,
in this case the instances are related, and could be seen as part of a single
instantiation:
\begin{spec}
  type instance FT aT bT where
    FT aT aT = TrueT
    FT aT bT = FalseT
\end{spec}
\Pedro{This syntax is not final. In particular, it is annoying that we have to
put |FT aT bT| at the top, but then ignore it since each case has all the
information we need. Alternatively, we could consider all instances in a module
as potentially overlapping, if some flag is switched on.}%
Such code should give rise to a single coercion only, with a kind that depends
on the type arguments:
\begin{spec}
  ax1 ::  {aT}     aT  aT  =>  FT aT aT  ~ TrueT
          {aT bT}  aT  bT  =>  FT aT bT  ~ FalseT
\end{spec}
The kind of this generalized axiom is taken from a sequence of possible
\emph{restricted axiom kinds}. Each restricted axiom kind has a list of
variables that it abstracts over, and then a sequence of type patterns. The
number of patterns tells us the arity of the coercion; all restricted axiom
kinds must have the same number of patterns. After the patterns comes a regular
axiom kind, of shape |aT ~ bT|. These kinds can mention the quantified
variables. The kind of the whole generalized axiom is the first restricted axiom
kind whose patterns can be matched against the arguments given. The coercion is
invalid if no such restricted axiom kind exists.

Consider another example:
\begin{spec}
  type instance GT aT bT where
    GT (cT,dT) Int  = cT
    GT Bool    bT   = bT
    GT aT      bT   = aT
\end{spec}
This group of instances gives rise to the following generalized axiom:
\begin{spec}
  ax2 ::  {cT dT}  (cT,dT)  Int  => GT (cT,dT) Int ~ cT
          {bT}     Bool     bT   => GT Bool bT ~ bT
          {aT bT}  aT       bT   => GT aT bT ~ aT
\end{spec}
For this to be possible we have to change the way type family instances are
translated into core coercion axioms, and also the structure of the axioms
themselves.

\section{How we can do it}
To support the new generalized axioms, we redefine the form of coercion
axioms in standard \FC to be:
\begin{spec}
C : OVER ({OVER alpha} (OVER tau) => Phi ~ Psi)
\end{spec}
The |OVER alpha| is the variables quantified over, and the |OVER tau| is the
list of patterns matched.
\Pedro{The use of the |=>| arrow does not intend to draw any parallels with
its use in standard Haskell.}%
Some restrictions apply to these patterns:
\begin{itemize}
\item A generalized axiom might consist of more than one alternative. In this
case, the number of patterns in each alternative must be the same.
\item Patterns cannot contain |forall EMPTY|.
\Pedro{At least; maybe more restrictions apply.}%
\end{itemize}

The typing rule for coercion axiom schemes follows:

\begin{displaymath}
\inferrule
  {|C : OVER ({OVER alpha} (OVER tau) => Phi ~ Psi) IN Gamma| \\
   |(i, Theta) = select (OVER gamma) (OVER (OVER tau))| }
  {|Gamma entails C (OVER gamma) : Theta (SUB Phi i) ~ Theta (SUB Psi i)| }
\end{displaymath}
\Pedro{Note that we're ignoring kinds for now, i.e.\ considering system \FC
instead of \FCP, for simplicity. I don't think kinds will complicate this matter
much.}%
The function |select| takes a list of arguments to the coercion, and the
patterns of the generalized coercion axiom, and returns the index of the first
matching pattern for the given arguments, and substitutions to apply to the
kind of the result. The number of arguments must be the same as the number of
types in each pattern. In case there is no successful match, the coercion is
ill-typed.

\subsection{Matching coercions}
Most of the work is deferred to |select|. Its task is to pick the index of the
first pattern that matches with the given coercions:
\begin{defn}[select]\label{def:select}
|(i, Theta) = select (OVER gamma) (OVER (OVER tau))| iff:
\begin{enumerate}
\item
  |OVER gamma| matches |SUB (OVER tau) i|
\item
  |Forall (j < i) (OVER gamma)| does not match |(SUB (OVER tau) j)|
\item
  |Theta ((SUB tau (i,j))) = (SUB gamma j|.
\end{enumerate}
\end{defn}

The following lemma must hold:
\begin{lem}[Selection consistency]\label{lem:select-consist}
Let |OVER gamma| and |OVER theta| be coercions such that for each
|(SUB gamma i) IN (OVER gamma)| and |(SUB theta i) IN (OVER theta)|,
|SUB gamma i| matches with |SUB theta i|.
If
|(i,_) = select (OVER gamma) (OVER (OVER tau))|, then 
|(i,_) = select (OVER theta) (OVER (OVER tau))|.
\end{lem}
For example, consider
|(OVER gamma) = (_:aT~bT) (_:REFL cT)| and
|(OVER theta) = (_:aT~Int) (_:REFL Bool)|.
If |select| returns a result for |OVER gamma|, then it must return the same
result for |OVER theta|.

Selection relies on the ability to match coercions against types.
For this we rely on standard type matching.
\begin{defn}[Matching coercions and types]\label{def:coercion-match}
|(OVER gamma) MATCHES (OVER tau) <=>|
|FOREACH (SUB gamma i : (SUB phi i) ~ (SUB psi i)) IN (OVER gamma)|,
|(SUB phi i) MATCHES (SUB tau i)|.
\end{defn}
\Pedro{I'm not really sure if this is the right thing to do here. It seems
rather arbitrary to just pick |SUB phi i|.}%

For example, recall the generalized axiom shown before:
\begin{spec}
  ax2 ::  {cT dT}  (cT,dT)  Int  => GT (cT,dT) Int ~ cT
          {bT}     Bool     bT   => GT Bool bT ~ bT
          {aT bT}  aT       bT   => GT aT bT ~ aT
\end{spec}
The following kinds hold:
\begin{spec}
ax2  (_:REFL Bool)        (_:REFL Bool)  : GT Bool Bool ~ Bool

ax2  (_:aT~Bool)          (_:Bool~aT)    : GT Bool aT ~ aT

ax2  (_:aT~Bool)          (_:aT~Bool)    : GT aT Bool ~ aT

ax2  (_:REFL (Bool,Int))  (_:REFL Int)   : GT (Bool,Int) Int ~ Bool
\end{spec}

\subsection{Type substitution}
The lemma for type substitution stays unchanged:
\begin{lem}[Type substitution in coercions]\label{lem:type-sub}
If
|Gamma entails gamma : Phi ~ Psi|,
|(alpha : eta) IN Gamma|, and
|Gamma entails beta : eta|, then
|Gamma entails gamma (SUBST beta alpha) :|
  |Phi (SUBST beta alpha) ~ Psi (SUBST beta alpha)|.
\end{lem}

Lemma \ref{lem:type-sub} is perhaps easier to visualize as follows:
\begin{displaymath}
\inferrule
  {|Gamma entails C (OVER gamma) : Phi ~ Psi| \\
   |(alpha : eta) IN Gamma| \\
   |Gamma entails beta : eta| }
  {|Gamma entails C (OVER gamma) (SUBST beta alpha) : Phi (SUBST beta alpha) ~ Psi (SUBST beta alpha)|}
\end{displaymath}

\subsection{Translation}
Recall the following restriction that applies to type family instances,
currently.
\Pedro{Simon, did I get this restriction right?}%
\begin{law}[Consistent instances]\label{law:consist-instances}
For any |FT|, |OVER (SUB alpha 1)|, |SUB beta 1|, |OVER (SUB alpha 2)|, and
|SUB beta 2| such that
\begin{spec}
type instance FT (OVER (SUB alpha 1)) = (SUB beta 1)
type instance FT (OVER (SUB alpha 2)) = (SUB beta 2)
\end{spec}
and for all |OVER sigma|, if |OVER sigma| unifies with |OVER (SUB alpha 1)| and
with |OVER (SUB alpha 2)| then 
|SUB beta 1| unifies with |SUB beta 2|.
\end{law}

Our generalized axioms do not need this restriction within each group. However,
we need the following restriction to guarantee that at most one group matches
any possible instantiation of a type family.
\begin{law}[Consistent instance groups]\label{law:consist-instance-groups}
For any |FT|, |OVER (SUB alpha 1)|, |OVER tau|, |sigma|, |OVER (SUB alpha 2)|,
|OVER phi|, and |psi| such that
\begin{spec}
type instance FT (OVER (SUB alpha 1)) where (OVER (FT (OVER tau) = sigma))
type instance FT (OVER (SUB alpha 2)) where (OVER (FT (OVER phi) = psi))
\end{spec}
for each |(OVER (SUB tau i)) IN (OVER (OVER tau))|,
for each |(OVER (SUB phi j)) IN (OVER (OVER phi))|, and
for all |OVER beta|,
if |OVER beta| unifies with |OVER (SUB tau i)| and with |OVER (SUB phi j)| then
|OVER (SUB sigma i)| unifies with |OVER (SUB psi j)|.
\end{law}


\bibliographystyle{plain}
\bibliography{CoSchemes}

\end{document}
