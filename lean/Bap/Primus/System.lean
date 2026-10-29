import Bap.Primus.Scheduler

namespace Bap.Primus

structure Job where
  name : String
  description : String := ""
  program : Bil.Program
  system : System := {}
  machine : Machine := {}

structure Result where
  finished : List Job := []
  failures : List (Job × String) := []
  machine : Machine

namespace Job

def enqueue (job : Job) (jobs : List Job) : List Job := jobs ++ [job]
def pending (jobs : List Job) : Nat := jobs.length

private def runJob (job : Job) : Except String (Machine × Bil.Effect) := do
  let machine ← Machine.init job.system job.machine
  Machine.run machine job.system job.program

def run (jobs : List Job) (initial : Machine) : Result :=
  jobs.foldl (init := ({ machine := initial } : Result)) fun result job =>
    match runJob job with
    | .ok (machine, _) => { result with finished := result.finished ++ [job], machine := machine }
    | .error error => { result with failures := result.failures ++ [(job, error)] }

end Job
end Bap.Primus
