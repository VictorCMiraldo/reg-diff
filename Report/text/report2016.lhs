\documentclass{article}
\usepackage[english]{babel}
\usepackage[a4paper]{geometry}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage[all]{xypic}
\usepackage{xcolor}
\usepackage{enumerate}
\usepackage{mathtools}
\usepackage{stmaryrd}
\usepackage{catchfilebetweentags}
\usepackage{code/excerpts/agda}

%% Margin specs

\geometry{margin=0.8in%
         ,top=0.2in%
         }

%% My commands

\newcommand{\TODO}[1]{%
\[ \bullet \text{\color{blue} #1} \] }

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda related stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% empty env, maybe later we can add some style to it.
\newenvironment{agdacode}[1][-2em]{%
\vspace{.5em}
\hspace{#1}
\begin{minipage}[t]{.8\textwidth}
}{%
\end{minipage}
\vspace{.5em}
}

\newcommand{\AgdaRaw}[2]{%
\ExecuteMetaData[code/excerpts/#1.tex]{#2}
}

\newcommand{\AgdaDots}{%
\hskip 3.5em \F{$\vdots$}
}

% Default code, no additional formatting.
\newcommand{\Agda}[2]{%
\begin{agdacode}
\AgdaRaw{#1}{#2}
\end{agdacode}
}

% Allows us to specify how much \hskip we want through #3.
\newcommand{\AgdaI}[3]{%
\begin{agdacode}[#3]
\AgdaRaw{#1}{#2}
\end{agdacode}
}

%% Agda shortcuts
\newcommand{\D}[1]{\AgdaDatatype{#1}}
\newcommand{\F}[1]{\AgdaFunction{#1}}
\newcommand{\K}[1]{\AgdaKeyword{#1}}
\newcommand{\N}[1]{\AgdaSymbol{#1}}
\newcommand{\RF}[1]{\AgdaField{#1}}
\newcommand{\IC}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\ICArgs}[2]{\AgdaInductiveConstructor{#1}$\; #2 $}
\newcommand{\DArgs}[2]{\D{#1}$\; #2 $}

\newcommand{\textrho}{$\rho$}
\newcommand{\textLambda}{$\Lambda$}
\newcommand{\textpi}{$\pi$}
\newcommand{\textmu}{$\mu$}
\newcommand{\textsigma}{$\sigma$}
\newcommand{\textSigma}{$\Sigma$}
\newcommand{\texteta}{$\eta$}
\newcommand{\textDelta}{$\Delta$}
\renewcommand{\textbeta}{$\beta$}

% And some others that actually require the unicode declaration
\DeclareUnicodeCharacter {10627}{\{\hspace {-.2em}[}
\DeclareUnicodeCharacter {10628}{]\hspace {-.2em}\}}
\DeclareUnicodeCharacter {8759}{::}
\DeclareUnicodeCharacter {8718}{$\square$}
\DeclareUnicodeCharacter {8799}{$\stackrel{\tiny ? \vspace{-1mm}}{=}$}
\DeclareUnicodeCharacter {8339}{$_x$}
\DeclareUnicodeCharacter {8336}{$_a$}
\DeclareUnicodeCharacter {7523}{$_r$}
\DeclareUnicodeCharacter {7506}{$^\circ$}
\DeclareUnicodeCharacter {8348}{$_t$}
\DeclareUnicodeCharacter {7522}{$_i$}
\DeclareUnicodeCharacter {119924}{$\mathcal{M}$}
\DeclareUnicodeCharacter {8346}{$_p$}
\DeclareUnicodeCharacter {8345}{$_n$}
\DeclareUnicodeCharacter {120028}{$\mathcal{M}$}

%%%%%%%%%%%%%%%%%%%%%%%%%%%

% lhs2TeX specifics

%include lhs2TeX.fmt 

\title{Diffing Mutually Recursive Types \\ \small{%
A code tour}}
\author{Victor Cacciari Miraldo \\ \small{%
University of Utrecht}}

\begin{document}
  \maketitle

\section{Our Universe}
  
  The universe we are using is a variant of Regular types,
but instead of having only one type variable, we handle $n$
type variables. The codes are description of regular functors on $n$ variables:

\Agda{RegDiff/Generic/Regular}{U-def}

  Constructor \IC{I} refers to the $n$-th type variable whereas \IC{K} refers
to a constant type. Value \textit{ks\#} is passed as a module parameter.
The denotation is defined as:

\Agda{RegDiff/Generic/Parms}{Parms-def}

\Agda{RegDiff/Generic/Regular}{U-denotation}

  A mutually recursive family can be easily encoded
in this setting. All we need is $n$ types that refer to $n$ type-variables
each!

\Agda{RegDiff/Generic/Multirec}{Fam-def}

\Agda{RegDiff/Generic/Multirec}{Fix-def}

  This universe is enough to model Context-Free grammars, and hence, provides
the basic barebones for diffing elements of an arbitrary programming language.
In the future, it could be interesting to see what kind of diffing functionality
indexed functors could provide, as these could have scoping rules and other
advanced features built into them. 

\subsection{Agda Details}

  As we mentioned above, our codes represent functors on $n$ variables. Obviously, to 
program with them, we need to apply these to something. The denotation receives a
function $\F{Fin}\;n \rightarrow \F{Set}$, denoted $\F{Parms}\;n$, which can be seen as a valuation for
each type variable.

\newcommand{\Interp}[2]{\F{$\llbracket$} #1 \F{$\rrbracket$}_{#2}}
  In the following sections, we will be dealing with values of $\Interp{ty}{A}$ for some class of valuations $A$, though.
We need to have decidable equality for $A\;k$ and some mapping from $A\;k$ to $\mathbb{N}$ for all $k$.
We call such valuations a \emph{well-behaved parameter}:

\Agda{RegDiff/Generic/Parms}{WBParms-def}

  In fact, the following sections discuss functionality that is completely independent from the aforementioned
parameters. We will be passing them as Agda module parameters. The first diffing technique we discuss
is the trivial diff. It's module is declared as follows:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-module-decl}

  We stick to this nomenclature throughtout the code. The first line handles constant types: 
\textit{ks\#} is how many constant types we have, $ks$ is the vector of such types and $keqs$ is an indexed 
vector with decidable equality over such types. The second line handles parameters: \textit{parms\#} is
how many type-variables our codes will have, $A$ is the valuation we are using and $WBA$ is a proof that
$A$ is \emph{well behaved}.

  We then declare the following synonyms:

\Agda{RegDiff/Diff/Trivial/Base}{Trivial-defs}

\section{Diffing}

  Intuitively, a \textit{Patch} is some description of a transformation, that can
be \textit{applied}, performing the described transformation and can be \textit{computed}, by
detecting how to transform one value into another.

  The easiest way to do so is using the diagonal functor:

\Agda{RegDiff/Diff/Trivial/Base}{delta-def}  
  

\section{Conclusion}
  
\end{document}
