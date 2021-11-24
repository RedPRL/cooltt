open Stdlib

type read
type write

type (_, 'a) t =
  | Null  : (write, 'a) t
  | Queue : { queue : 'a Queue.t; mutex : Mutex.t; has_jobs : Condition.t } -> ('mode, 'a) t

type 'a read_t = (read, 'a) t
type 'a write_t = (write, 'a) t

let create () : (read, 'a) t =
  let queue = Queue.create () in
  let mutex = Mutex.create () in
  let has_jobs = Condition.create () in
  Queue { queue; mutex; has_jobs }

let worker : (read, 'a) t -> (write, 'a) t =
  fun (Queue job_queue) -> Queue job_queue

let null = Null

let enqueue msg : (write, 'a) t -> unit =
  function
  | Queue job_queue ->
    Mutex.lock job_queue.mutex;
    Queue.add msg job_queue.queue;
    Condition.signal job_queue.has_jobs;
    Mutex.unlock job_queue.mutex
  | Null -> ()

let dequeue : (read, 'a) t -> 'a =
  fun (Queue job_queue) ->
  Mutex.lock job_queue.mutex;
  let msg =
    match Queue.take_opt job_queue.queue with
    | Some msg -> msg
    | None     ->
      Condition.wait job_queue.has_jobs job_queue.mutex;
      Queue.take job_queue.queue
  in
  Mutex.unlock job_queue.mutex;
  msg

let drain : (read, 'a) t -> 'a Seq.t =
  fun (Queue job_queue) ->
  Mutex.lock job_queue.mutex;
  let msgs = Queue.to_seq job_queue.queue in
  Queue.clear job_queue.queue;
  Mutex.unlock job_queue.mutex;
  msgs
