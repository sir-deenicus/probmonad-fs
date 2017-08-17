module FSharp.Probmonad
               
open Prelude.Math
open Prelude.Common
open System               
open Prelude   
open ProbCSharp

///////////
let prob = ProbBase.Prob

let uniformF (items:'a list) = ProbBase.UniformF (List.toArray items)
 
let categoricalF ps items = ProbBase.CategoricalF(Samples(Seq.zip items ps |> Seq.map (keepLeft prob >> ItemProb)))

let bernoulliF = ProbBase.Prob >> ProbBase.BernoulliF  

//******************

let dirichlet d = ProbBase.Dirichlet(Seq.toArray d)

let categorical ps items = ProbBase.Categorical(Samples(Seq.zip items ps |> Seq.map (keepLeft prob >> ItemProb)))

let categorical2 ps = ps |> Seq.toArray |> Array.map swap |> Array.unzip ||> categorical

let bernoulli (p:float) = ProbBase.Bernoulli p

let bernoulliOpts a b (p:float) = ProbBase.Bernoulli(p,a,b)
                                  
let beta α β = ProbBase.Beta(α, β)

let normal mean variance = ProbBase.Normal(mean,variance)

let mvnormal m v = ProbBase.MultiVariateNormal(m,v)

let lognormal mean variance = ProbBase.LogNormal(mean,variance)

let lognormal_mu mu sigma = ProbBase.LogNormalMu(mu,sigma)

let gamma shape rate = ProbBase.Gamma(shape,rate)

//*******************

let pdf  (d:Dist<float>) (x:float) = ProbBase.Pdf(d,x)  

let pdf2 (d:Dist<float[]>) (x:float[]) = ProbBase.Pdf(d,x)

let pmf d x = ProbBase.Pmf(d,x)         

let exactly p = ProbBase.Return(p)

let observe (f:'a -> Prob) dist =  ProbBase.Condition(f , dist) 

///////////////////

module Array =
  let groupBy f sq = Seq.groupBy f sq |> Seq.groupByResultToArrays

let roundAndGroupSamples r samples =
     samples 
     |> Seq.toArray 
     |> Array.map  (round r) 
     |> Array.groupBy id 
     |> Array.map (keepLeft (Array.length >> float))
     |> Array.normalizeWeights  
     

let roundAndGroupSamplesWith f  samples =
     samples 
     |> Seq.toArray 
     |> Array.map f
     |> Array.groupBy id 
     |> Array.map (keepLeft (Array.length >> float))
     |> Array.normalizeWeights           

//////////

type DistBuilder() =
    member __.Bind(x:Dist<_> , f) =  
      Bind<_, _>(x, fun a ->
                      Bind<_, _>(f(a), fun b -> Pure<_>(b) :> Dist<_> ) 
                      :> Dist<_>) 
                  :> Dist<_>
       
    member __.Delay(f) = f() 

    member __.Return (x:Dist<_>) = x // new FiniteDist<_>(Samples([x]));

    member __.ReturnFrom x = Pure<_> (x) :> Dist<_>


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

    member __.Zero () = new FiniteDist<_>(Samples([]))
 
    member __.Join items f = 
       let hd = Seq.head items
       let rest = Seq.skip 1 items
       rest |> Seq.fold (fun s v -> f s (__.Bind(v, __.ReturnFrom))) hd

/////////////////////

let fdist = FDistBuilder()

let dist = DistBuilder()

let prob2pair (p:ItemProb<_>)= p.Item, p.Prob.Value

let samplesToArray data = data |> Seq.toArray 
                               |> Array.mapFilter prob2pair (fun (_,p) -> not(p = 0.|| Double.IsNaN p || Double.IsInfinity p)) 
                               |> Array.normalizeWeights
 
let getImportanceSamples n (p:Dist<_>) = p.ImportanceSamples(n).Sample() |> samplesToArray |> Array.sortBy fst   

let rec computePosterior likelihood ps (p:Dist<_>) = function 
     | [] -> ps 
     | x::xs -> 
        let p' = p.Condition(fun theta -> likelihood theta x)
        
        computePosterior likelihood (p'::ps) p' xs  

///////////////////

let compactSamples nSamples = 
    nSamples                                     
    |> Seq.concat 
    |> Seq.toArray
    

let computeSamples nIters nPoints nSamples data =   
    let mutable nelements = 0

    [|for i in 0..nIters do                          
          let mh = MetropolisHastings.MHPrior(data, nPoints)        
          let samples = mh.SampleN(nSamples);
          let dat = Seq.take nSamples samples |> Seq.toArray |> compactSamples
        
          let els = Array.countElements dat
          nelements <- nelements + els.Count    

          yield (els)|]

    |> Array.fold (fun fm m -> Map.merge (+) id m fm) Map.empty 
    |> Map.toArray 

let computeCredible f roundTo p1 p2 dat =         
    let rec loop cumulativeProb ps = function
            | []  -> ps, cumulativeProb
            | _ when cumulativeProb > p2 -> ps, cumulativeProb
            | (x,p)::dat -> let ps' = if cumulativeProb + p < p1 then ps else ((x,p,round roundTo (p+cumulativeProb))::ps)
                            loop (cumulativeProb+p) ps' dat
    
    let cump, _ = loop 0. [] (List.ofSeq dat |> List.sortBy f)
    
    cump, List.maxBy third cump |> fst3, List.minBy third cump |> fst3

let smcSample nSamples nParticles (dist:Dist<_>) =
    let samples = dist.SmcMultiple(nSamples, nParticles).Sample()

    let wSamples = 
        [|for sample in samples -> sample.Item , sample.Prob.Value|] 
            |> Array.groupBy fst 
            |> Array.map (fun (x,xs) -> x, Array.sumBy snd xs)            

    wSamples, wSamples.Length

let compactMapSamples f samples =
    Array.map (fun (x,p:float) -> f x,p) samples
    |> Array.groupBy fst 
    |> Array.map (fun (x,xs) -> x, Array.sumBy snd xs) 
    |> Array.normalizeWeights  
    
let filterWith f data = 
  let matches = data |> Array.filter f
  (Array.length matches |> float) / (float data.Length) 

let inline computeDistrAverage f d = Array.sumBy (fun (x,p) -> f x * p) d


let smoothDistr alpha data = 
    data |> Array.fold (fun (p_prior,ps) (x,p) -> 
                  let p' = exponentialSmoothing id alpha p_prior p
                  p', (x,p')::ps) (snd data.[0],[])
         |> snd
         |> List.toArray
         |> Array.normalizeWeights

let compactFiniteSamples (d:FiniteDist<_>) = 
    d.Explicit.Weights 
    |> mapFilter prob2pair (snd >> (<>) 0.) 
    |> Seq.toArray 



let rec getLargeProbItems items cumulativeprob = function
        | [] -> items
        | _ when cumulativeprob > 0.5 -> items
        | ((_,p) as item::ps) -> getLargeProbItems (item::items) (p + cumulativeprob) ps

let findTopItem (vc:_[]) =
    let topindex,_ = vc |> Array.mapi (fun i x -> i,x) 
                        |> Array.maxBy (snd >> snd)
    let (_,p) as topitem = vc.[topindex]
    topindex, p , [topitem]
    

let getBulk (minp:float) items = 
    let rec loopinner cmin cmax bulkMass sum =
        if sum > minp || (cmin < 0 && cmax >= Array.length items) then sum, bulkMass 

        else  let bulkMass' = let frontpart = if cmin < 0 then bulkMass else items.[cmin]::bulkMass
                              frontpart@(if cmax > items.Length - 1 then [] else [items.[cmax]])       
              let currentSum = List.sumBy snd bulkMass'                   

              loopinner (cmin-1) (cmax+1) bulkMass' currentSum 

    let topindex,p,root = findTopItem items
    loopinner (topindex-1) (topindex+1) root p

let getBulkAlternating (minp:float) toggle items = 
    let rec loopinner toggle cmin cmax bulkMass sum =
        if sum > minp || (cmin < 0 && cmax >= Array.length items) then sum, bulkMass 
        else let cmin',cmax',bulkMass' = 
                 match toggle with 
                 | true -> cmin, cmax+1, if cmax > items.Length - 1 then bulkMass else bulkMass@[items.[cmax]] 
                 | false -> cmin-1, cmax, if cmin >= 0 then items.[cmin]::bulkMass else bulkMass
               
             let currentSum = List.sumBy snd bulkMass'                   

             loopinner (not toggle) cmin' cmax' bulkMass' currentSum  
    
    let topindex,p,root = findTopItem items
    loopinner toggle (topindex-1) (topindex+1) root p
