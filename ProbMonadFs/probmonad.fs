module FSharp.Probmonad
               
open Prelude.Math
open Prelude.Common
open System               
open Prelude   
open ProbCSharp
open Prelude.Common

///////////
let prob = ProbBase.Prob

let uniformF (items:'a list) = ProbBase.UniformF (List.toArray items)
 
let categoricalF ps items = ProbBase.CategoricalF(Samples(Seq.zip items ps |> Seq.map (keepLeft prob >> ItemProb)))

let bernoulliF = ProbBase.Prob >> ProbBase.BernoulliF  

//******************

let dirichlet d = ProbBase.Dirichlet(Seq.toArray d)

let categorical ps items = ProbBase.Categorical(items,ps) //(Samples(Seq.zip items ps |> Seq.map (keepLeft prob >> ItemProb)))

let categorical2 ps = ps |> Seq.toArray |> Array.map swap |> Array.unzip ||> categorical

let bernoulli (p:float) = ProbBase.Bernoulli p

let bernoulliOpts a b (p:float) = ProbBase.Bernoulli(p,a,b)
                                  
let beta α β = ProbBase.Beta(α, β)

let normal mean variance = ProbBase.Normal(mean,variance)

let mvnormal m v = ProbBase.MultiVariateNormal(m,v)

let lognormal mean variance = ProbBase.LogNormal(mean,variance)

let poisson lambda = ProbBase.Poisson(lambda)

let lognormal_mu mu sigma = ProbBase.LogNormalMu(mu,sigma)

let gamma shape rate = ProbBase.Gamma(shape,rate)

//*******************

let pdf  (d:Dist<float>) (x:float) = ProbBase.Pdf(d,x)  

let pdf2 (d:Dist<float[]>) (x:float[]) = ProbBase.Pdf(d,x)

let pmf (d:Dist<int>) x = ProbBase.Pmf(d,x)         

let pmf2 (d:Dist<'a>) x = ProbBase.Pmf(d,x)         

let exactly p = ProbBase.Return(p)

let observe (f:'a -> Prob) dist =  ProbBase.Condition(f , dist) 

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

/////////////////////

let fdist = FDistBuilder()

let dist = DistBuilder()

let prob2pair (p:ItemProb<_>)= p.Item, p.Prob.Value
                
let rec computePosterior likelihood ps (p:Dist<_>) = function 
     | [] -> ps 
     | x::xs -> 
        let p' = p.Condition(fun theta -> likelihood theta x)
        
        computePosterior likelihood (p'::ps) p' xs  

///////////////////    

let samplesToArray data = data |> Seq.toArray 
                               |> Array.mapFilter prob2pair (fun (_,p) -> not(p = 0.|| Double.IsNaN p || Double.IsInfinity p)) 
                               |> Array.normalizeWeights
 
let getImportanceSamples n (p:Dist<_>) = samplesToArray(p.ImportanceSamples(n).Sample())


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


let compactSamples nSamples = 
    nSamples                                     
    |> Seq.concat 
    |> Seq.toArray

let compactMapSamples f samples =
    Array.map (fun (x,p:float) -> f x,p) samples
    |> Array.groupBy fst 
    |> Array.map (fun (x,xs) -> x, Array.sumBy snd xs) 
    |> Array.normalizeWeights  


let compactFiniteSamples (d:FiniteDist<_>) = 
    d.Explicit.Weights 
    |> mapFilter prob2pair (snd >> (<>) 0.) 
    |> Seq.toArray  

    
let filterWith f data = 
  let matches = data |> Array.filter f
  (Array.length matches |> float) / (float data.Length) 
                       

let filterWithCondition conditional f data = 
  let sub = Array.filter conditional data
  let matches = sub |> Array.filter f 
  (Array.length matches |> float) / (float sub.Length) 


let inline probabilityOf filter m = 
    Array.sumBy snd (Array.filter (fun (k, _) -> filter k) m)


let inline conditionalProbability conditional matchwith m = 
    let sub = Array.filter (fun (k, _) -> conditional k) m
    let matches = Array.filter (fun (k, _) -> matchwith k) sub
    (Array.sumBy snd matches) / (Array.sumBy snd sub)

let toBits x = x / log 2. 

let inline log0 x = if x = 0. then 0. else log x

let inline entropy dist = -Seq.sumBy (fun (_,p) -> p * log0 p) dist

///////////////////////////////////

let smoothDistr alpha data = 
    data |> Array.fold (fun (p_prior,ps) (x,p) -> 
                  let p' = exponentialSmoothing id alpha p_prior p
                  p', (x,p')::ps) (snd data.[0],[])
         |> snd
         |> List.toArray
         |> Array.normalizeWeights

///////////////////////


let inline computeDistrAverage f d = Array.sumBy (fun (x,p) -> f x * p) d


let computeCredible f roundTo p1 p2 dat =         
    let rec loop cumulativeProb ps = function
            | []  -> ps, cumulativeProb
            | _ when cumulativeProb > p2 -> ps, cumulativeProb
            | (x,p)::dat -> let ps' = if cumulativeProb + p < p1 then ps else ((x,p,round roundTo (p+cumulativeProb))::ps)
                            loop (cumulativeProb+p) ps' dat
    
    let cump, _ = loop 0. [] (List.ofSeq dat |> List.sortBy f)
    
    cump,  List.minBy third cump |> fst3, List.maxBy third cump |> fst3


let getLargeProbItems maxp data =
    let rec innerloop curritems cumulativeprob = function
          | [] -> curritems
          | _ when cumulativeprob > maxp -> curritems
          | ((_,p) as item::ps) -> innerloop (item::curritems) (p + cumulativeprob) ps
    innerloop [] 0. data


let findTopItem (vc:_[]) =
    let topindex,_ = vc |> Array.indexed 
                        |> Array.maxBy (snd >> snd)
    let (_,p) as topitem = vc.[topindex]
    topindex, p , [topitem]
    

let getBulk (minp:float) items = 
    let rec loopinner cmin cmax bulkMass sum =
        if sum > minp || (cmin < 0 && cmax >= Array.length items) then sum, bulkMass 

        else  let bulkMass' = let frontpart = if cmin < 0 then bulkMass else items.[cmin]::bulkMass
                              if cmax > items.Length - 1 then frontpart else items.[cmax]::frontpart
              let currentSum = List.sumBy snd bulkMass'                   
              
              loopinner (cmin-1) (cmax+1) bulkMass' currentSum 

    let topindex,p,root = findTopItem items      
    loopinner (topindex-1) (topindex+1) root p


let getBulkAlternating (minp:float) toggle items = 
    let rec loopinner toggle cmin cmax bulkMass sum =
        if sum > minp || (cmin < 0 && cmax >= Array.length items) then sum, bulkMass 
        else let cmin',cmax',bulkMass' = 
                 match toggle with 
                 | true -> cmin, cmax+1, if cmax > items.Length - 1 then bulkMass else items.[cmax]::bulkMass 
                 | false -> cmin-1, cmax, if cmin >= 0 then items.[cmin]::bulkMass else bulkMass
               
             let currentSum = List.sumBy snd bulkMass'                   

             loopinner (not toggle) cmin' cmax' bulkMass' currentSum  
    
    let topindex,p,root = findTopItem items
    loopinner toggle (topindex-1) (topindex+1) root p

////////////////////////////////
    

let computeSamples nIters nPoints data = 
    let updaterate = max 1 (nIters / 10)
    let mutable nelements = 0

    [|for i in 0..nIters do                          
          let mh = MetropolisHastings.MHPrior(data, nPoints)        
          let samples = mh.SampleN(nPoints);
          let dat = Seq.takeOrMax nPoints samples |> Seq.toArray |> compactSamples
        
          let els = Array.countElements dat
          nelements <- nelements + els.Count
        
          if i % updaterate = 0 then 
              printfn "%d of %d" i nIters
              printfn "%d elements" nelements       
          yield (els)|]

    |> Array.fold (fun fm m -> Map.merge (+) id m fm) Map.empty 
    |> Map.toArray 


let smcSample nSamples nParticles (dist:Dist<_>) =
    let samples = dist.SmcMultiple(nSamples, nParticles).Sample()
         
    [|for sample in samples -> sample.Item , sample.Prob.Value|] 
          |> Array.groupBy fst 
          |> Array.map (fun (x,xs) -> x, Array.averageBy snd xs)            
            

let smcSamples nIters nSamples nParticles (dist:Dist<_>) =
    let updaterate = max 1 (nIters / 10)
    let mutable nelements = 0

    [|for i in 0..nIters do                                    
          let samples = smcSample nSamples nParticles dist |> Array.filter (snd >> (<) 1e-12)     
          nelements <- nelements + samples.Length
        
          if i % updaterate = 0 then 
              printfn "%d of %d" i nIters
              printfn "%d elements" nelements       
          yield (Map samples)|]

    |> Array.fold (fun fm m -> Map.merge (fun p1 p2 -> 0.5 * (p1 + p2)) id m fm) Map.empty 
    |> Map.toArray 

//////////////////////////////////


let inline betaMean (a,b) = a / (a + b)  

let inline dirichletMean (a:Map<_,_>) = let total = Map.sum a in Map.map (fun _ a_i -> a_i / total) a
 
let updateBeta (a,b) t =  if t then (a + 1., b) else (a, b + 1.)

let updateDirichlet (m:Map<_,_>) x = Map.add x (m.[x] + 1.) m
