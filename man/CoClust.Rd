\name{CoClust}
\alias{CoClust}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{Copula-Based Clustering Algorithm}
\description{
Cluster analysis based on copula functions
}
\usage{
CoClust(m, dimset = 2:5, nk = 12, copula = "frank", method.ma = 
  c("empirical", "pseudo"), method.c = c("ml", "mpl", "irho", "itau"),
  dfree=NULL, writeout = 10, ...)
}
 %- maybe also 'usage' for other objects documented here.
\arguments{
  \item{m}{a data matrix.}
  \item{dimset}{the set of dimensions for which the function tries the clustering.}
  \item{nk}{sample size of the set for selecting the number of clusters.}
  \item{copula}{a copula model. 
        This should be one of "normal", "t", "frank", "clayton" and "gumbel". See the Details section.}
  \item{method.ma}{estimation method for margins. See the Details section.}
  \item{method.c}{estimation method for copula. See \code{\link{fitCopula}}.}
  \item{dfree}{degrees of freedom for the \emph{t} copula.}
  \item{writeout}{writes a message on the number of allocated observations every writeout observations.}
  \item{\dots}{further parameters for \code{\link{fitCopula}}.}
}
\details{
\describe{
\item{Usage for Frank copula:}{.\cr
\code{CoClust(m, nmaxmarg = 2:5, nk = 12, copula = "frank",
method.ma=c("gaussian","empirical"), method.c = "mpl", ...)}}
}

CoClust is a clustering algorithm that, being based on copula functions, allows to group observations according to the multivariate dependence structure of the generating process without any assumptions on the margins.

For each \emph{k} in \code{dimset} the algorithm builds a sample of \code{nk} observations (rows of the data matrix \code{m}) by using the correlation matrix of Spearman's rho coefficients. 
The number of clusters \emph{K} is selected on the basis of the likelihood of the copula fit. Then, the remaining observations are allocated to the clusters as follows:
1. selects a \emph{K}-plet of observations on the basis of Spearman's rho; 2. allocates or discards the \emph{K}-plet on the basis of the likelihood of the copula fit.

The estimation approach for the copula fit is semiparametric: a range of nonparametric margins and parametric copula models can be selected by the user. 
The CoClust algorithm does not require to set a priori the number of clusters nor it needs a starting classification. 

Notice that the dependence structure for the Gaussian and the \emph{t} copula is set to exchangeable. Non structured dependence structures will be allowed in a future version.

}
 \value{An object of S4 class "CoClust", which is a list with the following elements:
    \item{Number.of.Clusters}{the number \emph{K} of identified clusters.}
    \item{Index.Matrix}{a \emph{n.obs} by \emph{(K+1)} matrix where \emph{n.obs} is the number of observations put in each cluster. The matrix contains the row indexes of the observations of the data matrix \code{m}. 
    The last column contains the log-likelihood of the copula fit.}
    \item{Data.Clusters}{the matrix of the final clustering.}
    \item{Dependence}{a list containing:
         \tabular{ll}{
        \code{Param}  \tab the estimated dependence parameter between clusters. \cr
        \code{Std.Err}\tab the standard error of Param.\cr
        \code{P.val}  \tab the p-value associated to the null hypothesis \code{H_0: theta=0}.\cr
        }}
    \item{LogLik}{the maximized log-likelihood copula fit.}
    \item{Est.Method}{the estimation method used for the copula fit.}
    \item{Opt.Method}{the optimization method used for the copula fit.}
    \item{BICk}{the value of the BIC for each \emph{k} in \code{dimset}.}
}
\note{
The final clustering is composed of \emph{k} groups in which observations of the same group are independent whereas the observations that belong to different groups and that form a \emph{K}-plet are dependent.
}
 \references{
Di Lascio, F.M.L. and Giannerini, S. (2012) "A Copula-Based Algorithm for Discovering Patterns of Dependent Observations", \emph{Journal of Classification}, Volume \bold{29}, Number 1 in press.

Di Lascio, F.M.L. (2008). "Analyzing the dependence structure of microarray data: a copula-based approach". \emph{PhD thesis}, Dipartimento di Scienze Statistiche, Universita' di Bologna, Italy.
}

\author{
Francesca Marta Lilja Di Lascio <francesca.dilascio@unibo.it>,

Simone Giannerini <simone.giannerini@unibo.it>}

\examples{
## ******************************************************************
## 1. build a 3-variate copula with different margins 
##    (Gaussian, Gamma, Beta)
##   
## 2. generate a data matrix xm with 15 rows and 21 columns and build 
##    the matrix of the true cluster indexes
##
## 3. apply the CoClust to the rows of xm and recover the multivariate
##    dependence structure of the data  
## ******************************************************************

## Step 1. **********************************************************
n      <- 105             # total number of observations
n.col  <- 21              # number of columns of the data matrix m 
n.marg <- 3               # dimension of the copula
n.row  <- n*n.marg/n.col  # number of rows of the data matrix m

theta  <- 10
copula <- frankCopula(theta, dim = n.marg)
mymvdc <- mvdc(copula, c("norm", "gamma", "beta"),list(list(mean=7, sd=2),
                list(shape=3, rate=4, scale=1/4), list(shape1=2, shape2=1)))

## Step 2. **********************************************************
set.seed(11)
x.samp <- rmvdc(mymvdc, n)
xm     <- matrix(x.samp, nrow = n.row, ncol = n.col, byrow=TRUE)

index.true <-  matrix(1:15,5,3)
colnames(index.true) <- c("Cluster 1","Cluster 2", "Cluster 3")

## Step 3. **********************************************************
clust <- CoClust(xm, dimset = 2:4, nk=8, copula="frank", 
                 method.ma="empirical", method.c="ml",writeout=1)
clust
clust@"Number.of.Clusters"
clust@"Dependence"$Param
clust@"Data.Clusters"
index.clust <- clust@"Index.Matrix"

## compare with index.true
index.clust
index.true
##
}
 % Add one or more standard keywords, see file 'KEYWORDS' in the % R documentation directory.
  \keyword{cluster}
  \keyword{multivariate}
