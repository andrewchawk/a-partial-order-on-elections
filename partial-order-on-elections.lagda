\begin{code}
open import Function
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Level
import Data.List.Relation.Unary.All as AllList
import Relation.Binary.PropositionalEquality as PropEqualityProps
\end{code}

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
      \item The qualities of the election importance relation \AgdaFunction{\AgdaUnderscore{}≤\AgdaUnderscore{}}
      \item \AgdaFunction{\AgdaUnderscore{}≤\AgdaUnderscore{}}
    \end{itemize}
    \item Prove\ldots{}
    \begin{itemize}
      \item That \AgdaFunction{\AgdaUnderscore{}≤\AgdaUnderscore{}} actually constitutes a partial order relation
      \item That \AgdaFunction{\AgdaUnderscore{}≤\AgdaUnderscore{}} has the defined qualities
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

\section{Base Types}

\begin{slide}{The Types of Types}
\begin{itemize}
  \item Election type, obviously
\begin{code}
Election : Set
\end{code}
  \item Candidate type
  \begin{itemize}
    \item Good for further definitions
  \end{itemize}
\begin{code}
Candidate : Set
\end{code}
\end{slide}

\begin{slide}{What Constitutes an Election?}
\begin{code}
Election = List Candidate
\end{code}
\end{slide}

\begin{slide}{But What Constitutes a Candidate of an Election?}
\begin{code}
Candidate = {!!}
\end{code}
\end{slide}

\begin{slide}{Necessary Qualities for Election Importance Relation}
\begin{itemize}
  \item For any given elections \(e_1\) and \(e_2\), if all candidates in \(e_1\) are identical and all candidates in \(e_2\) are effectively identical, then the importance of \(e_1\) is equal to the importance of \(e_2\).
  \begin{itemize}
    \item Elections on one effective candicate have the same
  \end{itemize}
  \item For any given election \(e\), if \(e\) has \emph{no} candidates, then \(e\) has the minimum possible importance.
  \begin{itemize}
    \item Null elections have minimum importance
  \end{itemize}
  \item For any given elections \(e_1\) and \(e_2\), if the maximum difference between candidates in \(e_1\) is less than the maximum difference between candidates in \(e_2\), then the importance of \(e_1\) is less than the importance of \(e_2\).
\end{itemize}
\end{slide}

\begin{code}
allInvolvedCandidates : Election -> List Candidate
allInvolvedCandidates = {!!}
\end{code}

\begin{code}
candidateEquality : Rel Candidate Level.zero
candidateEquality = {!!}
\end{code}

\begin{code}
dumbPartialOrder1 :
  IsPartialOrder {A = Election} _≡_ _≡_
dumbPartialOrder1 = record
  { isPreorder = PropEqualityProps.isPreorder
  ; antisym = λ x x₁ → sym x₁
  }

Real : Set
Real = {!!}

importance : Election -> Real
importance = {!!}

_<_ : Rel Real Level.zero
_<_ = {!!}

_≈_ : Rel Real Level.zero
_≈_ = {!!}
\end{code}

\begin{slide}{Any Election with a Single Effective Candidate is of a Single Importance}
\begin{code}
choices-between-identical-candidates-are-of-equal-importance :
  (e1 e2 : Election) ->
  AllList.All (\ c1 -> AllList.All (candidateEquality c1)
                                   (allInvolvedCandidates e1))
              (allInvolvedCandidates e1) ->
  AllList.All (\ c1 -> AllList.All (candidateEquality c1)
                                   (allInvolvedCandidates e2))
              (allInvolvedCandidates e2) ->
  importance e1 ≈ importance e2
choices-between-identical-candidates-are-of-equal-importance =
  {!!}
\end{code}
\end{slide}
\end{code}
