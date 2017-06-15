module FSharp.Probmonad
               
open Prelude.Math
open Prelude.Common
open System
open Prelude.SimpleGraphs
open Prelude                         


open ProbCSharp

///////////
let prob = ProbBase.Prob

let uniformF (items:'a list) = ProbBase.UniformF (List.toArray items)
 
let dirichlet d = ProbBase.Dirichlet(Seq.toArray d)
  
let categoricalF ps items = ProbBase.CategoricalF(Samples(Seq.zip items ps |> Seq.map (keepLeft prob >> ItemProb)))

let categorical ps items = ProbBase.Categorical(Samples(Seq.zip items ps |> Seq.map (keepLeft prob >> ItemProb)))

let categorical2 ps = ps |> Seq.toArray |> Array.map swap |> Array.unzip ||> categorical

let bernoulliF = ProbBase.Prob >> ProbBase.BernoulliF  

let bernoulli (p:float) = ProbBase.Bernoulli p

let normal mean variance = ProbBase.Normal(mean,variance)

let lognormal mean variance = ProbBase.LogNormal(mean,variance)

let lognormal_mu mu sigma = ProbBase.LogNormalMu(mu,sigma)

let gamma shape rate = ProbBase.Gamma(shape,rate)

let bernoulliOpts a b (p:float) = ProbBase.Bernoulli(p,a,b)

let pdf (d:Dist<float>) (x:float) = ProbBase.Pdf(d,x)

let pdf2 (d:PrimitiveDist<float>) (x:float) = ProbBase.Pdf(d,x)

let pdf3 (d:PrimitiveDist<float[]>) (x:float[]) = ProbBase.Pdf(d,x)

let pmf d x = ProbBase.Pmf(d,x)

let beta α β = ProbBase.Beta(α, β)

let exactly p = ProbBase.Return(p)

let observe (f:'a -> Prob) dist =  ProbBase.Condition(f , dist) 

///////////////////

let roundAndGroupSamples r samples =
     samples 
     |> Seq.toArray 
     |> Array.map  (round r) 
     |> Array.groupBy id 
     |> Array.map (keepLeft (Array.length >> float))
     |> Array.normalizeWeights  
     

     
let evpair a = a |> Array.fold (fun ev (c,p) -> p * c + ev) 0.

let calcEV choices prob =
     let p = Map.ofSeq prob

     choices |> Seq.fold (fun evt (opt, cost) -> p.[opt] * cost + evt) 0.

//////////

type DistBuilder() =
    member __.Bind(x:Dist<_> , f) =  
      Bind<_, _>(x, fun a ->
                      Bind<_, _>(f(a), fun b -> Pure<_>(b) :> Dist<_> ) 
                      :> Dist<_>) 
                  :> Dist<_>
       
    member __.Delay(f) = f() 

    member __.Return (x:Dist<_>) = x// new FiniteDist<_>(Samples([x]));

    member __.ReturnFrom x= Pure<_> (x) :> Dist<_>


type FDistBuilder() =
    member __.Bind(dist:FiniteDist<_> , f) = 
      let itemProbs = [|for probx in dist.Explicit.Weights do
                         let ydist = f(probx.Item) : FiniteDist<_>
                         for proby in ydist.Explicit.Weights do
                            yield ItemProb(proby.Item, probx.Prob.Mult(proby.Prob))|]

      FiniteDist<_>(Samples(itemProbs))

    member __.Delay(f) = f() 

    member __.Return (x:FiniteDist<_>) = x// new FiniteDist<_>(Samples([x]));

    member __.ReturnFrom x = new FiniteDist<_>(Samples([ItemProb(x, prob 1.)]))
    
    member __.Join items f = 
       let hd = Seq.head items
       let rest = Seq.tail items
       rest |> Seq.fold (fun s v -> f s (__.Bind(v, __.ReturnFrom))) hd

let fdist = FDistBuilder()

let dist = DistBuilder()

let prob2pair (p:ItemProb<_>)= p.Item, p.Prob.Value

let samplesToArray data = data |> Seq.toArray |> Array.map prob2pair

let getImportanceSamples n (p:Dist<_>) = p.ImportanceSamples(n).Sample() |> samplesToArray  |> Array.sortBy fst   


let rec computePosterior likelihood ps (p:Dist<_>) = function 
     | [] -> ps 
     | x::xs -> 
        let p' = p.Condition(fun theta -> likelihood theta x)
        
        computePosterior likelihood (p'::ps) p' xs

