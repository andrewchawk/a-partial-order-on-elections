\begin{abstract}
Extensively using Agda, the author presents a method of not-quite-programmatically ordering elections by importance.  Along the way, the author expands on this notion of ``importance'' while trying to be too abstract to really favor any political party or the like or even be worth a listen.  Huzzah!  The academic's dream is realized yet again!
\end{abstract}

\begin{slide}{Intent}
\begin{itemize}
  \item Main goal(s)
  \begin{itemize}
    \item Define an importance-based partial order on the elections in general
    \item Act like I don't know nobody
  \end{itemize}
  \item Necessary subgoals
  \begin{itemize}
    \item Define\ldots{}
    \begin{itemize}
      \item The type of all elections and additional relations, e.g., equality
      \item The qualities of the election importance relation \AgdaFunction{\AgdaUnderscore{}≤I\AgdaUnderscore{}}
      \item \AgdaFunction{\AgdaUnderscore{}≤I\AgdaUnderscore{}}
    \end{itemize}
    \item Prove\ldots{}
    \begin{itemize}
      \item That \AgdaFunction{\AgdaUnderscore{}≤I\AgdaUnderscore{}} actually constitutes a partial order relation
      \item That \AgdaFunction{\AgdaUnderscore{}≤I\AgdaUnderscore{}} has the defined qualities
    \end{itemize}
  \end{itemize}
\end{itemize}
\end{slide}

\begin{slide}{Justification}
\begin{itemize}
  \item Argument
  \begin{itemize}
    \item ``People think that every election will be the most important one!''
    \item ``Sure, all elections are \emph{equally important}.
    \item Speaker is a mathematician
    \begin{itemize}
      \item ``Hmm, fundamentally, what \emph{am} I trying to say?  How can I prove to myself that some elections are more important?''
      \item ``Hey, this problem is actually pretty abstract!''
    \end{itemize}
  \end{itemize}
\end{itemize}
\end{slide}

\begin{slide}{Agda Imports}
\begin{code}
open import Function
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Data.Product
open import Data.Sum

import Level
import Data.List.Relation.Unary.All as AllList
import Relation.Binary.PropositionalEquality as PropEqualityProps
\end{code}
\end{slide}

\begin{slide}{Cop-Out ``Definitions'' for Real Numbers}
\begin{code}
-- Non-negative real number type
Real : Set
Real = {!!}

-- | Less-than relation
_<_ : Rel Real Level.zero
_<_ = {!!}

-- | Equality relation -- real number equality is hairy
_≈_ : Rel Real Level.zero
_≈_ = {!!}

-- | Additive identity
0Real : Real
0Real = {!!}
\end{code}
\end{slide}

\begin{slide}{Properties of Real Numbers}
\begin{code}
≈-reflexivity : {x : Real} -> x ≈ x
≈-reflexivity = {!!}
\end{code}
\end{slide}

\begin{slide}{Nonnegative Real Numbers}
\begin{code}
-- | Nonnegative real number type
Real0 : Set
Real0 = Σ Real (\ r -> 0Real < r ⊎ r ≈ 0Real)

-- | Add positive sign
pos : Real0 -> Real
pos = proj₁
\end{code}

\begin{itemize}
  \item Will become important later
  \begin{itemize}
    \item Barely started
  \end{itemize}
\end{itemize}
\end{slide}

\section{Base Types}

\begin{slide}{The Types of Types}
\begin{itemize}
  \item Election type, obviously
\begin{code}
Election : {n : ℕ} -> Set
\end{code}
  \item Candidate type
  \begin{itemize}
    \item Good for further definitions
  \end{itemize}
\begin{code}
Candidate : ℕ -> Set
\end{code}
\end{slide}

\begin{slide}{What Constitutes an Election?}
\begin{code}
Election {n} = List (Candidate n)
\end{code}
\end{slide}

\section{The Election Importance Relation}

\begin{slide}{The Type of the Election Importance Relation}
\begin{code}
_≤I_ : {n : ℕ} -> Rel (Election {n}) Level.zero
\end{code}
\end{slide}

\begin{slide}{Necessary Qualities for Election Importance Relation}
\begin{itemize}
  \item Partial order
  \item For any given elections \(e_1\) and \(e_2\), if all candidates in \(e_1\) are identical and all candidates in \(e_2\) are effectively identical, then the importance of \(e_1\) is equal to the importance of \(e_2\).
  \begin{itemize}
    \item Elections on one effective candicate have the same
  \end{itemize}
  \item For any given election \(e\), if \(e\) has \emph{no} candidates, then \(e\) has the minimum possible importance.
  \begin{itemize}
    \item Null elections have minimum importance
  \end{itemize}
  \item For any given elections \(e_1\) and \(e_2\), if the maximum difference between candidates in \(e_1\) is less than the maximum difference between candidates in \(e_2\), then the importance of \(e_1\) is less than the importance of \(e_2\).
  \begin{itemize}
    \item Less different candidates have less important elections
  \end{itemize}
  \item Can be expressed as the ``application'' of the real number less-than-or-equal-to relation on the importances of elections
\end{itemize}
\end{slide}

\subsection{Defining Election Importance}

\begin{slide}{What is Election Importance?}
\begin{code}
importance : {n : ℕ} -> Election {n} -> Real0
\end{code}

\begin{itemize}
  \item Maximum difference between candidates in the candidate pool
  \begin{itemize}
    \item More formally, the difference between candidates \(c\) and \(d\) in the candidate pool such that for any other given candidates \(e\) and \(f\) in the same candidate pool, the difference between \(e\) and \(f\) is less than or equal to the difference between \(c\) and \(d\)
    \begin{itemize}
      \item Still not \emph{too} terribly formal
    \end{itemize}
  \end{itemize}
\end{itemize}
\end{slide}

\begin{slide}{Obvious Hairiness}
\begin{itemize}
  \item ``Difference between candidates''
  \begin{itemize}
    \item What consistutes difference?
    \item What even \emph{is} a candidate, really?
  \end{itemize}
\end{itemize}
\end{slide}

\subsection{Completing the Candidate Type}

\begin{slide}{The Hairy Solution}
\begin{code}
Candidate n = Vec Real n
\end{code}

\begin{itemize}
  \item Use of \AgdaDatatype{ℕ} justified, after all
  \item List of personality metrics, numerical political attributes, etc.
  \begin{itemize}
    \item Neuroticism
    \item Radicality
    \item Extent of fondness for club sandwiches
    \item Etc., etc.
    \item Try to limit to \emph{relevant} factors
    \begin{itemize}
      \item Subjective?
    \end{itemize}
  \end{itemize}
\end{itemize}
\end{slide}

\begin{slide}{The Candidate Difference Function}
\begin{code}
candidateDifference : {n : ℕ} -> Candidate n -> Candidate n -> Real0
candidateDifference = {!!}
\end{code}

\begin{itemize}
  \item Fundamentally just the \(n\)-dimensional distance function
\end{itemize}
\end{slide}

\begin{code}
candidateEquality : {n : ℕ} -> Rel (Candidate n) Level.zero
candidateEquality c1 c2 = pos (candidateDifference c1 c2) ≈ 0Real
\end{code}

\begin{code}
allInvolvedCandidates : {n : ℕ} -> Election {n} -> List (Candidate n)
allInvolvedCandidates e = e
\end{code}

\begin{code}
dumbPartialOrder1 :
  {n : ℕ} ->
  IsPartialOrder {A = Election {n}} _≡_ _≡_
dumbPartialOrder1 = record
  { isPreorder = PropEqualityProps.isPreorder
  ; antisym = λ x x₁ → sym x₁
  }

importance = {!!}
\end{code}

\begin{slide}{Any Election with No Candidates is Perfectly Unimportant}
\begin{code}
null-elections-suck :
  {n : ℕ} ->
  (e : Election {n}) ->
  length e ≡ 0 ->
  pos (importance e) ≈ 0Real
null-elections-suck = {!!}
\end{code}
\end{slide}

\begin{slide}{Any Election with a Single Effective Candidate is of a Single Importance}
\begin{code}
choices-between-identical-candidates-are-of-equal-importance :
  {n : ℕ} ->
  (e1 e2 : Election {n}) ->
  AllList.All (\ c1 -> AllList.All (candidateEquality c1)
                                   (allInvolvedCandidates e1))
              (allInvolvedCandidates e1) ->
  AllList.All (\ c1 -> AllList.All (candidateEquality c1)
                                   (allInvolvedCandidates e2))
              (allInvolvedCandidates e2) ->
  pos (importance e1) ≈ pos (importance e2)
choices-between-identical-candidates-are-of-equal-importance =
  {!!}

_≤I_ = {!!}
\end{code}
\end{slide}
