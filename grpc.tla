-------------------------------- MODULE grpc --------------------------------
(***************************************************************************)
(* Specification for the zebra-grpc crate design and it's relationship     *)
(* with the zebra-scanner crate and zebrad configuration file.             *)
(* It can handle the scan task functionality and how the grpc methods can  *)
(* add or delete information to the scanning database.                     *)
(*                                                                         *)
(* The spec is written in PlusCal and it's meant to be used with the TLC   *)
(* model checker.                                                          *)
(*                                                                         *)
(* The spec is divided in two parts: the first part is the PlusCal spec    *)
(* and the second part is translated TLA+ code.                            *)
(*                                                                         *)
(* The spec is divided in the following sections:                          *)
(*                                                                         *)
(* 1. Configuration Constants                                              *)
(* 2. Global Variables                                                     *)         
(* 3. Type Invariants                                                      *)
(* 4. Utility Functions                                                    *)
(* 5. gRPC Methods                                                         *)
(* 6. Services Process                                                     *)
(* 7. Scan Task Process                                                    *)
(* 8. Main Program Process                                                 *)
(*                                                                         *)
(* For more information visit:                                             *)
(* https://github.com/oxarbitrage/zebra-grpc-scan-spec)                    *)
(***************************************************************************)
EXTENDS TLC, Integers, Sequences, Randomization, FiniteSets, Json

\* CONFIGURATION CONSTANTS:

\* The set of keys as strings to be added to the scan task from the config file.
CONSTANT ConfigViewingKeys

\* We have 3 batches of keys so we can try different combinations, including
\* duplicated keys.

\* A set of keys as strings.
CONSTANT GrpcViewingKeysBatch1
\* A second set of keys as strings.
CONSTANT GrpcViewingKeysBatch2
\* A third set of keys as strings.
CONSTANT GrpcViewingKeysBatch3
\* The maximum number of scan tasks that can be added to the scan task set.
CONSTANT MaxScanTasks

\* GLOBAL VARIABLES:

\* A sequence of batches with keys to call grpc methods. Currently we have 3 batches.
GrpcViewingKeys == <<GrpcViewingKeysBatch1, GrpcViewingKeysBatch2, GrpcViewingKeysBatch3>>

\* A dummy response to an `Info` request.
info_response == ToJson([saplingheight |-> 1])
\* A random list of transations to be used as a `Results` response.
results_response == ToJson([transactions |-> RandomSetOfSubsets(1, 3, 1..10)])
 \* An empty response to `Register`.
register_response == ToJson([empty |-> {}])
\* An empty response to `Delete`.
delete_response == ToJson([empty |-> {}])
\* An empty response to `Clear`.
clear_response == ToJson([empty |-> {}])
\* An empty response to `Subscribe`. TODO: which should be a channel with updates.
subscribe_response == ToJson([empty |-> {}])
\* An empty response to `Status`. TODO: which should have some data from the scan task for the key.
status_response == ToJson([empty |-> {}])
\* The set of statuses a scan task can be on at any given time.
scan_task_statuses == {"waiting", "adding", "deleting"}
\* The set of valid service requests.
service_requests == {"waiting", "info", "results", "clear", "status", "register", "delete", "subscribe"}

(*--algorithm grpc
variables
    \* The scan tasks are a set that is initially empty.
    scan_tasks = {};
    \* A string that will be used as a response to any of the gRPC method calls.
    response = "";
    \* The status of the scan task, initially listening.
    scan_task_status = "waiting";
    (* A key to be passed to any of the services, and also added or deleted to/from
       the scan task at a given instant, initially empty. *)
    key_to_be_served = "";
    \* The current service request flag.
    service_request = "waiting";
    \* The number of batches the configuration has.
    number_of_batches = 0;
    \* The counter for the number of batches.
    counter = 1;

define
    \* THE TYPE INVARIANT:
    TypeInvariant ==
        \* The response is always in the STRING domain
        /\ response \in STRING
        \* The scan task status is always in the scan task statuses set.
        /\ scan_task_status \in scan_task_statuses
        \* The key to be served is always in the STRING domain.
        /\ key_to_be_served \in STRING
        \* The service request is always in the service requests set.
        /\ service_request \in service_requests
    \* LIVENESS PROPERTIES:
    ScanTaskLiveness ==
        \* The ScanTask process always reachs a waiting state.
        <>(scan_task_status = "waiting")
    ServiceLiveness ==
        \* The Services process always reachs a waiting state.
        <>(service_request = "waiting")
end define;

\* UTILITY FUNCTIONS::

\* Helper function to get the number of non empty batches the configuration has. 
procedure get_config_number_of_batches()
begin
    CheckBatch1:
        if GrpcViewingKeysBatch1 # {} then
            number_of_batches := number_of_batches + 1;
        end if;
    CheckBatch2:
        if GrpcViewingKeysBatch2 # {} then
            number_of_batches := number_of_batches + 1;
        end if;
    CheckBatch3:
        if GrpcViewingKeysBatch3 # {} then
            number_of_batches := number_of_batches + 1;
        end if;
        return;
end procedure;

\* Call the scan task to add keys coming from the config file.
procedure add_config_keys(keys)
begin
    AddConfigKeys:
        with key \in keys do
            key_to_be_served := key;
            scan_task_status := "adding";
            return;
        end with;
end procedure;

\* GRPC METHODS:

\* The `get_info` grpc method.
procedure get_info()
begin
    InfoServiceRequest:
        service_request := "info";
        return;
end procedure;

\* The `get_results` grpc method.
procedure get_results(keys)
begin
    ResultsServiceRequest:
        with key \in keys do
            key_to_be_served := key;
            service_request := "results";
            return;
        end with;
end procedure;

\* The `clear_results` grpc method.
procedure clear_results(keys)
begin
    ClearServiceRequest:
        with key \in keys do
            key_to_be_served := key;
            service_request := "clear";
            return;
        end with;
end procedure;

\* The `get_status` grpc method.
procedure get_status(keys)
begin
    StatusServiceRequest:
        with key \in keys do
            key_to_be_served := key;
            service_request := "status";
            return;
        end with;
end procedure;

\* The `register_keys` grpc method.
procedure register_keys(keys)
begin
    RegisterServiceRequest:
        with key \in keys do
            key_to_be_served := key;
            service_request := "register";
            return;
        end with;
end procedure;

\* The `delete_keys` grpc method.
procedure delete_keys(keys)
begin
    DeleteServiceRequest:
        with key \in keys do
            key_to_be_served := key;
            service_request := "delete";
            return;
        end with;
end procedure;

\* The `scan` grpc method.
\* The method call 3 services one next to the other.
procedure scan(keys)
begin
    RegisterServiceRequestFromScan:
        with key \in keys do
            key_to_be_served := key;
            service_request := "register";
        end with;
    ResultsServiceRequestFromScan:
        with key \in keys do
            key_to_be_served := key;
            service_request := "results";
        end with;
    SubscribeServiceRequestFromScan:
        with key \in keys do
            key_to_be_served := key;
            service_request := "subscribe";
            return;
        end with;
end procedure;

\* SERVICES PROCESS:

\* Listen for requests, send requests to scan task where is needed and provide responses.
process services = "SERVICES"
begin
    Services:
        if service_request = "info" then
            Info:
                response := info_response;
        elsif service_request = "results" then
            Results:
                if key_to_be_served \in scan_tasks then
                    response := results_response;
                else
                    response := "Error: key not found.";
                end if;
        elsif service_request = "clear" then
            Clear:
                if key_to_be_served \in scan_tasks then
                    response := clear_response;
                else
                    response := "Error: key not found.";
                end if;
        elsif service_request = "status" then
            Status:
                if key_to_be_served \in scan_tasks then
                    response := status_response;
                else
                    response := "Error: key not found.";
                end if;
        elsif service_request = "register" then
            Register:
                if key_to_be_served \in scan_tasks then
                    KeyError:
                        response := "Error: key already in scan task.";
                else
                    Success:
                        scan_task_status := "adding";
                        response := register_response;
                end if;
        elsif service_request = "delete" then
            Delete:
                if key_to_be_served \in scan_tasks then
                    scan_task_status := "deleting";
                    response := delete_response;
                else
                    response := "Error: key not found.";
                end if;
        elsif service_request = "subscribe" then
            Subscribe:
                if key_to_be_served \in scan_tasks then
                    response := subscribe_response;
                else
                    response := "Error: key not found.";
                end if;
        end if;
    ClearRequestFlag:
        service_request := "waiting";
    \* Make the process loops forever.
    ServicesLoop:
        goto Services;
end process;

\* SCAN TASK PROCESS:

\* Listen for requests from the services process, add or remove tasks to the scan task set.
fair process scantask = "SCAN TASK"
variables inner_state = {};
begin
    GetScanTasks:
        inner_state := scan_tasks;
    ScanTask:
        if Cardinality(scan_tasks) > MaxScanTasks then
            BoundError:
                response := "Error: max scan tasks reached.";
                scan_task_status := "waiting";
        elsif scan_task_status = "adding" then
            Adding:
                inner_state := inner_state \union {key_to_be_served};
                scan_task_status := "waiting";
        elsif scan_task_status = "deleting" then
            Deleting:
                scan_tasks := scan_tasks \ {key_to_be_served};
                scan_task_status := "waiting";
        end if;
    StoreScanTasks:
        scan_tasks := inner_state;
    \* Make the process loops forever.
    ScanTaskLoop:
        goto ScanTask;
end process;

\* MAIN PROCESS:

\* Calls all grpc methods with the given keys.
process Main = "MAIN"
begin
    ConfigGuard:
        if ConfigViewingKeys # {} then
            FromZebradConfig:
                call add_config_keys(ConfigViewingKeys);
        end if;
    ListeningGuard:
        if GrpcViewingKeys # <<>> then
            GetTotalIterationsToMake:
                call get_config_number_of_batches();
            ListeningMode:
                while counter <= number_of_batches do
                    GetInfoCall:
                        call get_info();
                    RegisterKeysCall:
                        call register_keys(GrpcViewingKeys[counter]);
                    GetStatusCall:
                        call get_status(GrpcViewingKeys[counter]);
                    GetResultsCall:
                        call get_results(GrpcViewingKeys[counter]);
                    ClearResultsCall:
                        call clear_results(GrpcViewingKeys[counter]);
                    DeleteKeysCall:
                        call delete_keys(GrpcViewingKeys[counter]);
                    ScanCall:
                        call scan(GrpcViewingKeys[counter]);
                    IncrementCounter:
                        counter := counter + 1;
                end while;
                goto End;
        end if;
    End:
        skip;
        
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f6c668a3" /\ chksum(tla) = "48d8f3a2")
\* Parameter keys of procedure add_config_keys at line 130 col 27 changed to keys_
\* Parameter keys of procedure get_results at line 151 col 23 changed to keys_g
\* Parameter keys of procedure clear_results at line 162 col 25 changed to keys_c
\* Parameter keys of procedure get_status at line 173 col 22 changed to keys_ge
\* Parameter keys of procedure register_keys at line 184 col 25 changed to keys_r
\* Parameter keys of procedure delete_keys at line 195 col 23 changed to keys_d
CONSTANT defaultInitValue
VARIABLES scan_tasks, response, scan_task_status, key_to_be_served, 
          service_request, number_of_batches, counter, pc, stack

(* define statement *)
TypeInvariant ==

    /\ response \in STRING

    /\ scan_task_status \in scan_task_statuses

    /\ key_to_be_served \in STRING

    /\ service_request \in service_requests

ScanTaskLiveness ==

    <>(scan_task_status = "waiting")
ServiceLiveness ==

    <>(service_request = "waiting")

VARIABLES keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys, inner_state

vars == << scan_tasks, response, scan_task_status, key_to_be_served, 
           service_request, number_of_batches, counter, pc, stack, keys_, 
           keys_g, keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

ProcSet == {"SERVICES"} \cup {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ scan_tasks = {}
        /\ response = ""
        /\ scan_task_status = "waiting"
        /\ key_to_be_served = ""
        /\ service_request = "waiting"
        /\ number_of_batches = 0
        /\ counter = 1
        (* Procedure add_config_keys *)
        /\ keys_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_results *)
        /\ keys_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure clear_results *)
        /\ keys_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_status *)
        /\ keys_ge = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure register_keys *)
        /\ keys_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure delete_keys *)
        /\ keys_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure scan *)
        /\ keys = [ self \in ProcSet |-> defaultInitValue]
        (* Process scantask *)
        /\ inner_state = {}
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "SERVICES" -> "Services"
                                        [] self = "SCAN TASK" -> "GetScanTasks"
                                        [] self = "MAIN" -> "ConfigGuard"]

CheckBatch1(self) == /\ pc[self] = "CheckBatch1"
                     /\ IF GrpcViewingKeysBatch1 # {}
                           THEN /\ number_of_batches' = number_of_batches + 1
                           ELSE /\ TRUE
                                /\ UNCHANGED number_of_batches
                     /\ pc' = [pc EXCEPT ![self] = "CheckBatch2"]
                     /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                     key_to_be_served, service_request, 
                                     counter, stack, keys_, keys_g, keys_c, 
                                     keys_ge, keys_r, keys_d, keys, 
                                     inner_state >>

CheckBatch2(self) == /\ pc[self] = "CheckBatch2"
                     /\ IF GrpcViewingKeysBatch2 # {}
                           THEN /\ number_of_batches' = number_of_batches + 1
                           ELSE /\ TRUE
                                /\ UNCHANGED number_of_batches
                     /\ pc' = [pc EXCEPT ![self] = "CheckBatch3"]
                     /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                     key_to_be_served, service_request, 
                                     counter, stack, keys_, keys_g, keys_c, 
                                     keys_ge, keys_r, keys_d, keys, 
                                     inner_state >>

CheckBatch3(self) == /\ pc[self] = "CheckBatch3"
                     /\ IF GrpcViewingKeysBatch3 # {}
                           THEN /\ number_of_batches' = number_of_batches + 1
                           ELSE /\ TRUE
                                /\ UNCHANGED number_of_batches
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                     key_to_be_served, service_request, 
                                     counter, keys_, keys_g, keys_c, keys_ge, 
                                     keys_r, keys_d, keys, inner_state >>

get_config_number_of_batches(self) == CheckBatch1(self)
                                         \/ CheckBatch2(self)
                                         \/ CheckBatch3(self)

AddConfigKeys(self) == /\ pc[self] = "AddConfigKeys"
                       /\ \E key \in keys_[self]:
                            /\ key_to_be_served' = key
                            /\ scan_task_status' = "adding"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ keys_' = [keys_ EXCEPT ![self] = Head(stack[self]).keys_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << scan_tasks, response, service_request, 
                                       number_of_batches, counter, keys_g, 
                                       keys_c, keys_ge, keys_r, keys_d, keys, 
                                       inner_state >>

add_config_keys(self) == AddConfigKeys(self)

InfoServiceRequest(self) == /\ pc[self] = "InfoServiceRequest"
                            /\ service_request' = "info"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << scan_tasks, response, 
                                            scan_task_status, key_to_be_served, 
                                            number_of_batches, counter, keys_, 
                                            keys_g, keys_c, keys_ge, keys_r, 
                                            keys_d, keys, inner_state >>

get_info(self) == InfoServiceRequest(self)

ResultsServiceRequest(self) == /\ pc[self] = "ResultsServiceRequest"
                               /\ \E key \in keys_g[self]:
                                    /\ key_to_be_served' = key
                                    /\ service_request' = "results"
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ keys_g' = [keys_g EXCEPT ![self] = Head(stack[self]).keys_g]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << scan_tasks, response, 
                                               scan_task_status, 
                                               number_of_batches, counter, 
                                               keys_, keys_c, keys_ge, keys_r, 
                                               keys_d, keys, inner_state >>

get_results(self) == ResultsServiceRequest(self)

ClearServiceRequest(self) == /\ pc[self] = "ClearServiceRequest"
                             /\ \E key \in keys_c[self]:
                                  /\ key_to_be_served' = key
                                  /\ service_request' = "clear"
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ keys_c' = [keys_c EXCEPT ![self] = Head(stack[self]).keys_c]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << scan_tasks, response, 
                                             scan_task_status, 
                                             number_of_batches, counter, keys_, 
                                             keys_g, keys_ge, keys_r, keys_d, 
                                             keys, inner_state >>

clear_results(self) == ClearServiceRequest(self)

StatusServiceRequest(self) == /\ pc[self] = "StatusServiceRequest"
                              /\ \E key \in keys_ge[self]:
                                   /\ key_to_be_served' = key
                                   /\ service_request' = "status"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ keys_ge' = [keys_ge EXCEPT ![self] = Head(stack[self]).keys_ge]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, 
                                              number_of_batches, counter, 
                                              keys_, keys_g, keys_c, keys_r, 
                                              keys_d, keys, inner_state >>

get_status(self) == StatusServiceRequest(self)

RegisterServiceRequest(self) == /\ pc[self] = "RegisterServiceRequest"
                                /\ \E key \in keys_r[self]:
                                     /\ key_to_be_served' = key
                                     /\ service_request' = "register"
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ keys_r' = [keys_r EXCEPT ![self] = Head(stack[self]).keys_r]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << scan_tasks, response, 
                                                scan_task_status, 
                                                number_of_batches, counter, 
                                                keys_, keys_g, keys_c, keys_ge, 
                                                keys_d, keys, inner_state >>

register_keys(self) == RegisterServiceRequest(self)

DeleteServiceRequest(self) == /\ pc[self] = "DeleteServiceRequest"
                              /\ \E key \in keys_d[self]:
                                   /\ key_to_be_served' = key
                                   /\ service_request' = "delete"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ keys_d' = [keys_d EXCEPT ![self] = Head(stack[self]).keys_d]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, 
                                              number_of_batches, counter, 
                                              keys_, keys_g, keys_c, keys_ge, 
                                              keys_r, keys, inner_state >>

delete_keys(self) == DeleteServiceRequest(self)

RegisterServiceRequestFromScan(self) == /\ pc[self] = "RegisterServiceRequestFromScan"
                                        /\ \E key \in keys[self]:
                                             /\ key_to_be_served' = key
                                             /\ service_request' = "register"
                                        /\ pc' = [pc EXCEPT ![self] = "ResultsServiceRequestFromScan"]
                                        /\ UNCHANGED << scan_tasks, response, 
                                                        scan_task_status, 
                                                        number_of_batches, 
                                                        counter, stack, keys_, 
                                                        keys_g, keys_c, 
                                                        keys_ge, keys_r, 
                                                        keys_d, keys, 
                                                        inner_state >>

ResultsServiceRequestFromScan(self) == /\ pc[self] = "ResultsServiceRequestFromScan"
                                       /\ \E key \in keys[self]:
                                            /\ key_to_be_served' = key
                                            /\ service_request' = "results"
                                       /\ pc' = [pc EXCEPT ![self] = "SubscribeServiceRequestFromScan"]
                                       /\ UNCHANGED << scan_tasks, response, 
                                                       scan_task_status, 
                                                       number_of_batches, 
                                                       counter, stack, keys_, 
                                                       keys_g, keys_c, keys_ge, 
                                                       keys_r, keys_d, keys, 
                                                       inner_state >>

SubscribeServiceRequestFromScan(self) == /\ pc[self] = "SubscribeServiceRequestFromScan"
                                         /\ \E key \in keys[self]:
                                              /\ key_to_be_served' = key
                                              /\ service_request' = "subscribe"
                                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ keys' = [keys EXCEPT ![self] = Head(stack[self]).keys]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED << scan_tasks, response, 
                                                         scan_task_status, 
                                                         number_of_batches, 
                                                         counter, keys_, 
                                                         keys_g, keys_c, 
                                                         keys_ge, keys_r, 
                                                         keys_d, inner_state >>

scan(self) == RegisterServiceRequestFromScan(self)
                 \/ ResultsServiceRequestFromScan(self)
                 \/ SubscribeServiceRequestFromScan(self)

Services == /\ pc["SERVICES"] = "Services"
            /\ IF service_request = "info"
                  THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Info"]
                  ELSE /\ IF service_request = "results"
                             THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Results"]
                             ELSE /\ IF service_request = "clear"
                                        THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Clear"]
                                        ELSE /\ IF service_request = "status"
                                                   THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Status"]
                                                   ELSE /\ IF service_request = "register"
                                                              THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Register"]
                                                              ELSE /\ IF service_request = "delete"
                                                                         THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Delete"]
                                                                         ELSE /\ IF service_request = "subscribe"
                                                                                    THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Subscribe"]
                                                                                    ELSE /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_served, service_request, 
                            number_of_batches, counter, stack, keys_, keys_g, 
                            keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

Info == /\ pc["SERVICES"] = "Info"
        /\ response' = info_response
        /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
        /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                        service_request, number_of_batches, counter, stack, 
                        keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                        inner_state >>

Results == /\ pc["SERVICES"] = "Results"
           /\ IF key_to_be_served \in scan_tasks
                 THEN /\ response' = results_response
                 ELSE /\ response' = "Error: key not found."
           /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
           /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                           service_request, number_of_batches, counter, stack, 
                           keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, 
                           keys, inner_state >>

Clear == /\ pc["SERVICES"] = "Clear"
         /\ IF key_to_be_served \in scan_tasks
               THEN /\ response' = clear_response
               ELSE /\ response' = "Error: key not found."
         /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
         /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                         service_request, number_of_batches, counter, stack, 
                         keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                         inner_state >>

Status == /\ pc["SERVICES"] = "Status"
          /\ IF key_to_be_served \in scan_tasks
                THEN /\ response' = status_response
                ELSE /\ response' = "Error: key not found."
          /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
          /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                          service_request, number_of_batches, counter, stack, 
                          keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                          inner_state >>

Register == /\ pc["SERVICES"] = "Register"
            /\ IF key_to_be_served \in scan_tasks
                  THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "KeyError"]
                  ELSE /\ pc' = [pc EXCEPT !["SERVICES"] = "Success"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_served, service_request, 
                            number_of_batches, counter, stack, keys_, keys_g, 
                            keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

KeyError == /\ pc["SERVICES"] = "KeyError"
            /\ response' = "Error: key already in scan task."
            /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
            /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                            service_request, number_of_batches, counter, stack, 
                            keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, 
                            keys, inner_state >>

Success == /\ pc["SERVICES"] = "Success"
           /\ scan_task_status' = "adding"
           /\ response' = register_response
           /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
           /\ UNCHANGED << scan_tasks, key_to_be_served, service_request, 
                           number_of_batches, counter, stack, keys_, keys_g, 
                           keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

Delete == /\ pc["SERVICES"] = "Delete"
          /\ IF key_to_be_served \in scan_tasks
                THEN /\ scan_task_status' = "deleting"
                     /\ response' = delete_response
                ELSE /\ response' = "Error: key not found."
                     /\ UNCHANGED scan_task_status
          /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
          /\ UNCHANGED << scan_tasks, key_to_be_served, service_request, 
                          number_of_batches, counter, stack, keys_, keys_g, 
                          keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

Subscribe == /\ pc["SERVICES"] = "Subscribe"
             /\ IF key_to_be_served \in scan_tasks
                   THEN /\ response' = subscribe_response
                   ELSE /\ response' = "Error: key not found."
             /\ pc' = [pc EXCEPT !["SERVICES"] = "ClearRequestFlag"]
             /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                             service_request, number_of_batches, counter, 
                             stack, keys_, keys_g, keys_c, keys_ge, keys_r, 
                             keys_d, keys, inner_state >>

ClearRequestFlag == /\ pc["SERVICES"] = "ClearRequestFlag"
                    /\ service_request' = "waiting"
                    /\ pc' = [pc EXCEPT !["SERVICES"] = "ServicesLoop"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, number_of_batches, 
                                    counter, stack, keys_, keys_g, keys_c, 
                                    keys_ge, keys_r, keys_d, keys, inner_state >>

ServicesLoop == /\ pc["SERVICES"] = "ServicesLoop"
                /\ pc' = [pc EXCEPT !["SERVICES"] = "Services"]
                /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                key_to_be_served, service_request, 
                                number_of_batches, counter, stack, keys_, 
                                keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                                inner_state >>

services == Services \/ Info \/ Results \/ Clear \/ Status \/ Register
               \/ KeyError \/ Success \/ Delete \/ Subscribe
               \/ ClearRequestFlag \/ ServicesLoop

GetScanTasks == /\ pc["SCAN TASK"] = "GetScanTasks"
                /\ inner_state' = scan_tasks
                /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTask"]
                /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                key_to_be_served, service_request, 
                                number_of_batches, counter, stack, keys_, 
                                keys_g, keys_c, keys_ge, keys_r, keys_d, keys >>

ScanTask == /\ pc["SCAN TASK"] = "ScanTask"
            /\ IF Cardinality(scan_tasks) > MaxScanTasks
                  THEN /\ pc' = [pc EXCEPT !["SCAN TASK"] = "BoundError"]
                  ELSE /\ IF scan_task_status = "adding"
                             THEN /\ pc' = [pc EXCEPT !["SCAN TASK"] = "Adding"]
                             ELSE /\ IF scan_task_status = "deleting"
                                        THEN /\ pc' = [pc EXCEPT !["SCAN TASK"] = "Deleting"]
                                        ELSE /\ pc' = [pc EXCEPT !["SCAN TASK"] = "StoreScanTasks"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_served, service_request, 
                            number_of_batches, counter, stack, keys_, keys_g, 
                            keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

BoundError == /\ pc["SCAN TASK"] = "BoundError"
              /\ response' = "Error: max scan tasks reached."
              /\ scan_task_status' = "waiting"
              /\ pc' = [pc EXCEPT !["SCAN TASK"] = "StoreScanTasks"]
              /\ UNCHANGED << scan_tasks, key_to_be_served, service_request, 
                              number_of_batches, counter, stack, keys_, keys_g, 
                              keys_c, keys_ge, keys_r, keys_d, keys, 
                              inner_state >>

Adding == /\ pc["SCAN TASK"] = "Adding"
          /\ inner_state' = (inner_state \union {key_to_be_served})
          /\ scan_task_status' = "waiting"
          /\ pc' = [pc EXCEPT !["SCAN TASK"] = "StoreScanTasks"]
          /\ UNCHANGED << scan_tasks, response, key_to_be_served, 
                          service_request, number_of_batches, counter, stack, 
                          keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys >>

Deleting == /\ pc["SCAN TASK"] = "Deleting"
            /\ scan_tasks' = scan_tasks \ {key_to_be_served}
            /\ scan_task_status' = "waiting"
            /\ pc' = [pc EXCEPT !["SCAN TASK"] = "StoreScanTasks"]
            /\ UNCHANGED << response, key_to_be_served, service_request, 
                            number_of_batches, counter, stack, keys_, keys_g, 
                            keys_c, keys_ge, keys_r, keys_d, keys, inner_state >>

StoreScanTasks == /\ pc["SCAN TASK"] = "StoreScanTasks"
                  /\ scan_tasks' = inner_state
                  /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTaskLoop"]
                  /\ UNCHANGED << response, scan_task_status, key_to_be_served, 
                                  service_request, number_of_batches, counter, 
                                  stack, keys_, keys_g, keys_c, keys_ge, 
                                  keys_r, keys_d, keys, inner_state >>

ScanTaskLoop == /\ pc["SCAN TASK"] = "ScanTaskLoop"
                /\ pc' = [pc EXCEPT !["SCAN TASK"] = "ScanTask"]
                /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                key_to_be_served, service_request, 
                                number_of_batches, counter, stack, keys_, 
                                keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                                inner_state >>

scantask == GetScanTasks \/ ScanTask \/ BoundError \/ Adding \/ Deleting
               \/ StoreScanTasks \/ ScanTaskLoop

ConfigGuard == /\ pc["MAIN"] = "ConfigGuard"
               /\ IF ConfigViewingKeys # {}
                     THEN /\ pc' = [pc EXCEPT !["MAIN"] = "FromZebradConfig"]
                     ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_served, service_request, 
                               number_of_batches, counter, stack, keys_, 
                               keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                               inner_state >>

FromZebradConfig == /\ pc["MAIN"] = "FromZebradConfig"
                    /\ /\ keys_' = [keys_ EXCEPT !["MAIN"] = ConfigViewingKeys]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "add_config_keys",
                                                                  pc        |->  "ListeningGuard",
                                                                  keys_     |->  keys_["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "AddConfigKeys"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, 
                                    number_of_batches, counter, keys_g, keys_c, 
                                    keys_ge, keys_r, keys_d, keys, inner_state >>

ListeningGuard == /\ pc["MAIN"] = "ListeningGuard"
                  /\ IF GrpcViewingKeys # <<>>
                        THEN /\ pc' = [pc EXCEPT !["MAIN"] = "GetTotalIterationsToMake"]
                        ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "End"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, 
                                  number_of_batches, counter, stack, keys_, 
                                  keys_g, keys_c, keys_ge, keys_r, keys_d, 
                                  keys, inner_state >>

GetTotalIterationsToMake == /\ pc["MAIN"] = "GetTotalIterationsToMake"
                            /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_config_number_of_batches",
                                                                       pc        |->  "ListeningMode" ] >>
                                                                   \o stack["MAIN"]]
                            /\ pc' = [pc EXCEPT !["MAIN"] = "CheckBatch1"]
                            /\ UNCHANGED << scan_tasks, response, 
                                            scan_task_status, key_to_be_served, 
                                            service_request, number_of_batches, 
                                            counter, keys_, keys_g, keys_c, 
                                            keys_ge, keys_r, keys_d, keys, 
                                            inner_state >>

ListeningMode == /\ pc["MAIN"] = "ListeningMode"
                 /\ IF counter <= number_of_batches
                       THEN /\ pc' = [pc EXCEPT !["MAIN"] = "GetInfoCall"]
                       ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "End"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_served, service_request, 
                                 number_of_batches, counter, stack, keys_, 
                                 keys_g, keys_c, keys_ge, keys_r, keys_d, keys, 
                                 inner_state >>

GetInfoCall == /\ pc["MAIN"] = "GetInfoCall"
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_info",
                                                          pc        |->  "RegisterKeysCall" ] >>
                                                      \o stack["MAIN"]]
               /\ pc' = [pc EXCEPT !["MAIN"] = "InfoServiceRequest"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_served, service_request, 
                               number_of_batches, counter, keys_, keys_g, 
                               keys_c, keys_ge, keys_r, keys_d, keys, 
                               inner_state >>

RegisterKeysCall == /\ pc["MAIN"] = "RegisterKeysCall"
                    /\ /\ keys_r' = [keys_r EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "register_keys",
                                                                  pc        |->  "GetStatusCall",
                                                                  keys_r    |->  keys_r["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, 
                                    number_of_batches, counter, keys_, keys_g, 
                                    keys_c, keys_ge, keys_d, keys, inner_state >>

GetStatusCall == /\ pc["MAIN"] = "GetStatusCall"
                 /\ /\ keys_ge' = [keys_ge EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                    /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_status",
                                                               pc        |->  "GetResultsCall",
                                                               keys_ge   |->  keys_ge["MAIN"] ] >>
                                                           \o stack["MAIN"]]
                 /\ pc' = [pc EXCEPT !["MAIN"] = "StatusServiceRequest"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_served, service_request, 
                                 number_of_batches, counter, keys_, keys_g, 
                                 keys_c, keys_r, keys_d, keys, inner_state >>

GetResultsCall == /\ pc["MAIN"] = "GetResultsCall"
                  /\ /\ keys_g' = [keys_g EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_results",
                                                                pc        |->  "ClearResultsCall",
                                                                keys_g    |->  keys_g["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "ResultsServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, 
                                  number_of_batches, counter, keys_, keys_c, 
                                  keys_ge, keys_r, keys_d, keys, inner_state >>

ClearResultsCall == /\ pc["MAIN"] = "ClearResultsCall"
                    /\ /\ keys_c' = [keys_c EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "clear_results",
                                                                  pc        |->  "DeleteKeysCall",
                                                                  keys_c    |->  keys_c["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ClearServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, 
                                    number_of_batches, counter, keys_, keys_g, 
                                    keys_ge, keys_r, keys_d, keys, inner_state >>

DeleteKeysCall == /\ pc["MAIN"] = "DeleteKeysCall"
                  /\ /\ keys_d' = [keys_d EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "delete_keys",
                                                                pc        |->  "ScanCall",
                                                                keys_d    |->  keys_d["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, 
                                  number_of_batches, counter, keys_, keys_g, 
                                  keys_c, keys_ge, keys_r, keys, inner_state >>

ScanCall == /\ pc["MAIN"] = "ScanCall"
            /\ /\ keys' = [keys EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "scan",
                                                          pc        |->  "IncrementCounter",
                                                          keys      |->  keys["MAIN"] ] >>
                                                      \o stack["MAIN"]]
            /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequestFromScan"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_served, service_request, 
                            number_of_batches, counter, keys_, keys_g, keys_c, 
                            keys_ge, keys_r, keys_d, inner_state >>

IncrementCounter == /\ pc["MAIN"] = "IncrementCounter"
                    /\ counter' = counter + 1
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningMode"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, 
                                    number_of_batches, stack, keys_, keys_g, 
                                    keys_c, keys_ge, keys_r, keys_d, keys, 
                                    inner_state >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                       key_to_be_served, service_request, number_of_batches, 
                       counter, stack, keys_, keys_g, keys_c, keys_ge, keys_r, 
                       keys_d, keys, inner_state >>

Main == ConfigGuard \/ FromZebradConfig \/ ListeningGuard
           \/ GetTotalIterationsToMake \/ ListeningMode \/ GetInfoCall
           \/ RegisterKeysCall \/ GetStatusCall \/ GetResultsCall
           \/ ClearResultsCall \/ DeleteKeysCall \/ ScanCall
           \/ IncrementCounter \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == services \/ scantask \/ Main
           \/ (\E self \in ProcSet:  \/ get_config_number_of_batches(self)
                                     \/ add_config_keys(self) \/ get_info(self)
                                     \/ get_results(self) \/ clear_results(self)
                                     \/ get_status(self) \/ register_keys(self)
                                     \/ delete_keys(self) \/ scan(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(scantask)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Mar 07 18:13:46 UYT 2024 by alfredo
\* Created Wed Feb 21 10:40:53 UYT 2024 by alfredo
