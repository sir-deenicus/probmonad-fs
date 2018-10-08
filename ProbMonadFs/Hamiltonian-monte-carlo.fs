module Probmonad.HamiltonianMonteCarlo

//Hamiltonian monte carlo, hacky start

open DiffSharp.AD.Float32

//contains code from http://diffsharp.github.io/DiffSharp/examples-hamiltonianmontecarlo.html

let normal = MathNet.Numerics.Distributions.Normal(0.,1.)
let Rnd = new System.Random()

// Uniform random number ~U(0, 1)
let rnd() = Rnd.NextDouble() |> float32

// Leapfrog integrator
// u: potential energy function
// k: kinetic energy function
// d: integration step size
// steps: number of integration steps
// (x0, p0): initial position and momentum vectors
let leapFrog (u:DV->D) (k:DV->D) (d:D) steps (x0, p0) =
    let hd = d / 2.f
    [1..steps] 
    |> List.fold (fun (x, p) _ ->
        let p' = p - hd * grad u x
        let x' = x + d * grad k p'
        x', p' - hd * grad u x') (x0, p0)

// Hamiltonian Monte Carlo
// hdelta: step size for Hamiltonian dynamics
// hsteps: number of steps for Hamiltonian dynamics
// x0: initial state
// f: target distribution function
let hmc hdelta hsteps (x0:DV) (f:DV->D) =
    let u x = -log (f x) // potential energy
    let k p = (p * p) / D 2.f // kinetic energy
    let hamiltonian x p = u x + k p
    let p = DV.init x0.Length (fun _ -> normal.Sample())
    let x', p' = leapFrog u k (D hdelta) hsteps (x0, p) 
    if rnd() < float32 (exp ((hamiltonian x0 p) - (hamiltonian x' p'))) then x' else x0

module Densities =
  let rec factorial acc (x:D) = if x = D 1.f then x else factorial (acc * x) (x - 1.f) 

  // Multivariate normal distribution (any dimension)
  // mu: mean vector
  // sigma: covariance matrix
  // x: variable vector
  let multiNormal (mu:DV) (sigmaInverse:DM) (x:DV) = 
      let xm = x - mu
      exp (-(xm * sigmaInverse * xm) / D 2.f)

  let normal (mu : D) (sigma : D) (xv:DV) =
      let x = xv.[0]
      exp (-(x - mu) ** 2.f / (D 2.f * sigma ** 2.f))

  let lognormal (mu : D) (sigma : D) (xv:DV) = normal mu sigma (log xv)

  let gamma (shape) (rate) (xv:DV) = let x = xv.[0] in x ** (shape - 1.f) * exp (-rate * x)

  let poisson lambda (kvec:DV) = let k = kvec.[0] in lambda ** k/ (factorial (D 1.f) k) 

  let exponential λ (x:DV) = exp (-λ * x.[0])

  let studentT loc scale deg (xv:DV) =
      let x = xv.[0]
      (D 1.f + D 1.f/deg * ((x - loc)/scale) ** 2.f) ** -((deg + 1.f) / 2.f)
            

///Prior can be of the form where points is an array of parameters for each sampled from distr
///let prior (a,b) hmc =
///    let x = hmc a (Densities.multiNormal [] [])
///    let y = hmc b (Densities.gamma 2.f 5.f)
///    (x,y)  
let drawSamples n hdelta hsteps prior x0  =
    Seq.unfold (fun parameters -> 
      let parameters' = prior parameters (hmc hdelta hsteps)    
      Some(parameters', parameters')) x0 
      |> Seq.take n 
      |> Seq.toArray 

let update density data = 
    Seq.fold (fun ps point -> ps + log (density point)) 0. data

let conditionalUpdates pdf samples data =
    samples |> Array.map (fun (parameters) ->   
      parameters, update (pdf parameters) data) 

let extractPosteriorSamples likelihoods f =  
       Array.groupBy f likelihoods 
    |> Array.map (fun (t,ts) -> t, Array.sumBy (snd>>exp) ts) 
