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
        \describe{
            \item{\code{Model}}{the copula model used for the clustering.}
            \item{\code{Param}}{the estimated dependence parameter between clusters.}
            \item{\code{Std.Err}}{the standard error of Param.}
            \item{\code{P.val}}{the p-value associated to the null hypothesis \code{H_0: theta=0}.}
        }}
    \item{\code{LogLik}:}{Object of class \code{"numeric"}. The maximized log-likelihood copula fit.}
    \item{\code{Est.Method}:}{Object of class \code{"character"}. The estimation method used for the copula fit.}
    \item{\code{Opt.Method}:}{Object of class \code{"character"}. The optimization method used for the copula fit.}
    \item{\code{LLC}:}{Object of class \code{"numeric"}. The value of the LogLikelihood Criterion for each \emph{k} in \code{dimset}.}
    \item{\code{Index.dimset}:}{Object of class \code{"list"}. A list that, for each \emph{k} in \code{dimset}, contains the index matrix of the initial set of \code{nk} observations used for selecting the number of clusters, together with the associated loglikelihood.}
  }
}
\section{Methods}{
No methods defined with class "CoClust" in the signature.
}
 \references{
Di Lascio, F.M.L. and Giannerini, S. (2019). "Clustering dependent observations with copula functions". \emph{Statistical Papers}, 60, p.35-51. DOI 10.1007/s00362-016-0822-3.

Di Lascio, F.M.L. (2018) "CoClust: An R Package for Copula-based Cluster Analysis", Recent Applications in Data Clustering, p.93-114. Ed. Harun Pirim, IntTech Publisher. ISBN 978-1-78923-527-2. DOI 10.5772/intechopen.74865.

Di Lascio, F.M.L., Durante, F. and Pappada', R. (2017). "Copula-based clustering methods", Copulas and Dependence Models with Applications, p.49-67. Eds Ubeda-Flores, M., de Amo, E., Durante, F. and Fernandez Sanchez, J., Springer International Publishing. ISBN: 978-3-319-64220-8.

Di Lascio, F.M.L. and Disegna, M. (2017). "A copula-based clustering algorithm to analyse EU country diets". \emph{Knowledge-Based Systems}, 132, p.72-84. DOI: 10.1016/j.knosys.2017.06.004.

Di Lascio, F.M.L. and Giannerini, S. (2012). "A Copula-Based Algorithm for Discovering Patterns of Dependent Observations", \emph{Journal of Classification}, 29(1), p.50-75.

Di Lascio, F.M.L. (2008). "Analyzing the dependence structure of microarray data: a copula-based approach". \emph{PhD thesis}, Dipartimento di Scienze Statistiche, Universita' di Bologna, Italy.
}

\author{Francesca Marta Lilja Di Lascio <marta.dilascio@unibz.it>,

Simone Giannerini <simone.giannerini@unibo.it>}


\seealso{
    See Also \code{\link[CoClust]{CoClust}}.
}
\examples{
showClass("CoClust")
}
\keyword{classes}
