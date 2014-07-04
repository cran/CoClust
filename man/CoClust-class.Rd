\name{CoClust-class}
\docType{class}
\alias{CoClust-class}

\title{Class "CoClust"}
\description{A class for \code{CoClust} and its extensions}
\section{Objects from the Class}{
Objects can be created by calls of the form \code{new("CoClust", ...)}.
}
\section{Slots}{
     \describe{
    \item{\code{Number.of.Clusters}:}{Object of class \code{"integer"}. The number \emph{K} of identified clusters.}
    \item{\code{Index.Matrix}:}{Object of class \code{"matrix"}. A \emph{n.obs} by \emph{(K+1)} matrix where \emph{n.obs} is the number of observations put in each cluster. The matrix contains the row indexes of the observations of the data matrix \code{m}.
    The last column contains the log-likelihood of the copula fit.}
    \item{\code{Data.Clusters}:}{Object of class \code{"matrix"}. The matrix of the final clustering.}
    \item{\code{Dependence}:}{Object of class \code{"list"}. The list contains:
    \tabular{ll}{
        \code{Model}  \tab the copula model used for the clustering. \cr
        \code{Param}  \tab the estimated dependence parameter between clusters. \cr
        \code{Std.Err}\tab the standard error of Param.\cr
        \code{P.val}  \tab the p-value associated to the null hypothesis \code{H_0: theta=0}.\cr
        }
    }
    \item{\code{LogLik}:}{Object of class \code{"numeric"}. The maximized log-likelihood copula fit.}
    \item{Est.Method}{Object of class \code{"character"}. The estimation method used for the copula fit.}
    \item{Opt.Method}{Object of class \code{"character"}. The optimization method used for the copula fit.}
    \item{LLC}{Object of class \code{"numeric"}. The value of the LogLikelihood Criterion for each \emph{k} in \code{dimset}.}
    \item{Index.dimset}{Object of class \code{"list"}. A list that, for each \emph{k} in \code{dimset}, contains the index matrix of the initial set of \code{nk} observations used for selecting the number of clusters, together with the associated loglikelihood.}
  }
}
\section{Methods}{
No methods defined with class "CoClust" in the signature.
}
 \references{
Di Lascio, F.M.L. and Giannerini, S. (2014) "An Improved Copula-Based Clustering Algorithm", \emph{Working Paper}.

Di Lascio, F.M.L. and Giannerini, S. (2012) "A Copula-Based Algorithm for Discovering Patterns of Dependent Observations", \emph{Journal of Classification}, Volume \bold{29}, Number 1, 50-75.

Di Lascio, F.M.L. (2008). "Analyzing the dependence structure of microarray data: a copula-based approach". \emph{PhD thesis}, Dipartimento di Scienze Statistiche, Universita' di Bologna, Italy.
}

\author{Francesca Marta Lilja Di Lascio <marta.dilascio@unibz.it>,

Simone Giannerini <simone.giannerini@unibo.it>}


\seealso{
    See Also \code{\link{CoClust}} and \code{\linkS4class{copula}}.
}
\examples{
showClass("CoClust")
}
\keyword{classes}
