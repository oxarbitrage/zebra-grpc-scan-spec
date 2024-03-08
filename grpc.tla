-------------------------------- MODULE grpc --------------------------------
EXTENDS TLC, Integers, Sequences, Randomization

\* CONFIGURATION CONSTANTS:

\* The set of keys as strings to be added to the scan task from the config file.
CONSTANT ConfigViewingKeys

\* We have 3 batches of keys so we can try different combinations, including
\* duplicated keys.

\* A set of keys as strings to be added to the scan task by calling grpc methods.
CONSTANT GrpcViewingKeysBatch1
\* A second set of keys as strings to be added to the scan task by calling grpc methods.
CONSTANT GrpcViewingKeysBatch2
\* A third of keys as strings to be added to the scan task by calling grpc methods.
CONSTANT GrpcViewingKeysBatch3

\* GLOBAL VARIABLES:

GrpcViewingKeys == <<GrpcViewingKeysBatch1, GrpcViewingKeysBatch2, GrpcViewingKeysBatch3>>

\* A dummy response to an `Info` request.
info_response == [saplingheight |-> 1]
\* A random list of transations to be used as a `Results` response.
results_response == [transactions |-> RandomSetOfSubsets(1, 3, 1..10)]
 \* An empty response to `Register`.
register_response == [empty |-> {}]
\* An empty response to `Delete`.
delete_response == [empty |-> {}]
\* An empty response to `Clear`.
clear_response == [empty |-> {}]
\* An empty response to `Subscribe`. TODO: which should be a channel with updates.
subscribe_response == [empty |-> {}]
\* An empty response to `Status`. TODO: which should have some data from the scan task for the key.
status_response == [empty |-> {}]
\* The set of statuses a scan task can be on at any given time.
scan_task_statuses == {"waiting", "adding", "deleting"}
\* The set of valid service requests.
service_requests == {"waiting", "adding", "deleting"}

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
    service_request = "none";

    counter = 1;

\* The type invariants.
define
  TypeInvariant ==
    \* The response is always in the STRING domain
    /\ response \in STRING
    \* The scan task status is always in the scan task statuses set.
    /\ scan_task_status \in scan_task_statuses
    \* The key to be served is always in the STRING domain.
    /\ key_to_be_served \in STRING
    \* The service request is always in the service requests set.
    /\ service_request \in service_requests
end define;

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
        end with;
        return;
end procedure;

\* The services process make requests to services and provide responses.
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
                response := "Error: key already in scan task.";
            else
                scan_task_status := "adding";
                response := register_response;
            end if;
    elsif service_request = "delete" then
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
    else 
        skip;
    end if;
end process;

\* The scan task process, in charge of adding and removing tasks to the scan task set.
process scantask = "SCAN TASK"
begin
  AddTask:
    if scan_task_status = "adding" then
        \*await scan_tasks = {};
        scan_tasks := scan_tasks \union {key_to_be_served};
        scan_task_status := "waiting";
    elsif scan_task_status = "deleting" then
        \*await scan_tasks # <<>>;
        scan_tasks := scan_tasks \ {key_to_be_served};
        scan_task_status := "waiting";
    else 
        skip;
    end if;
end process;

\* The main program process.
process Main = "MAIN"
begin
    ConfigGuard:
        if ConfigViewingKeys # {} then
            FromZebradConfig:
                either call add_config_keys(ConfigViewingKeys); or skip; end either;
        end if;
    ListeningGuard:
        if GrpcViewingKeys # <<>> then
            ListeningMode:
                while counter <= Len(GrpcViewingKeys) do
                    either GetInfoCall:
                        call get_info();
                    or GetResultsCall:
                        call get_results(GrpcViewingKeys[counter]);
                    or RegisterKeysCall:
                        call register_keys(GrpcViewingKeys[counter]);
                    or DeleteKeysCall:
                        call delete_keys(GrpcViewingKeys[counter]);
                    or ClearResultsCall:
                        call clear_results(GrpcViewingKeys[counter]);
                    or ScanCall:
                        call scan(GrpcViewingKeys[counter]);
                    or GetStatusCall:
                        call get_status(GrpcViewingKeys[counter]);
                    end either;
                    IncrementCounter:
                        counter := counter + 1;
                end while;
            End:
                skip;
        end if;
        
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1a14ba0e" /\ chksum(tla) = "a85c1d85")
\* Parameter keys of procedure add_config_keys at line 72 col 27 changed to keys_
\* Parameter keys of procedure get_results at line 91 col 23 changed to keys_g
\* Parameter keys of procedure clear_results at line 102 col 25 changed to keys_c
\* Parameter keys of procedure get_status at line 113 col 22 changed to keys_ge
\* Parameter keys of procedure register_keys at line 124 col 25 changed to keys_r
\* Parameter keys of procedure delete_keys at line 135 col 23 changed to keys_d
CONSTANT defaultInitValue
VARIABLES scan_tasks, response, scan_task_status, key_to_be_served, 
          service_request, counter, pc, stack

(* define statement *)
TypeInvariant ==

  /\ response \in STRING

  /\ scan_task_status \in scan_task_statuses

  /\ key_to_be_served \in STRING

  /\ service_request \in service_requests

VARIABLES keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys

vars == << scan_tasks, response, scan_task_status, key_to_be_served, 
           service_request, counter, pc, stack, keys_, keys_g, keys_c, 
           keys_ge, keys_r, keys_d, keys >>

ProcSet == {"SERVICES"} \cup {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ scan_tasks = {}
        /\ response = ""
        /\ scan_task_status = "waiting"
        /\ key_to_be_served = ""
        /\ service_request = "none"
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
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "SERVICES" -> "Services"
                                        [] self = "SCAN TASK" -> "AddTask"
                                        [] self = "MAIN" -> "ConfigGuard"]

AddConfigKeys(self) == /\ pc[self] = "AddConfigKeys"
                       /\ \E key \in keys_[self]:
                            /\ key_to_be_served' = key
                            /\ scan_task_status' = "adding"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ keys_' = [keys_ EXCEPT ![self] = Head(stack[self]).keys_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << scan_tasks, response, service_request, 
                                       counter, keys_g, keys_c, keys_ge, 
                                       keys_r, keys_d, keys >>

add_config_keys(self) == AddConfigKeys(self)

InfoServiceRequest(self) == /\ pc[self] = "InfoServiceRequest"
                            /\ service_request' = "info"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << scan_tasks, response, 
                                            scan_task_status, key_to_be_served, 
                                            counter, keys_, keys_g, keys_c, 
                                            keys_ge, keys_r, keys_d, keys >>

get_info(self) == InfoServiceRequest(self)

ResultsServiceRequest(self) == /\ pc[self] = "ResultsServiceRequest"
                               /\ \E key \in keys_g[self]:
                                    /\ key_to_be_served' = key
                                    /\ service_request' = "results"
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ keys_g' = [keys_g EXCEPT ![self] = Head(stack[self]).keys_g]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << scan_tasks, response, 
                                               scan_task_status, counter, 
                                               keys_, keys_c, keys_ge, keys_r, 
                                               keys_d, keys >>

get_results(self) == ResultsServiceRequest(self)

ClearServiceRequest(self) == /\ pc[self] = "ClearServiceRequest"
                             /\ \E key \in keys_c[self]:
                                  /\ key_to_be_served' = key
                                  /\ service_request' = "clear"
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ keys_c' = [keys_c EXCEPT ![self] = Head(stack[self]).keys_c]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << scan_tasks, response, 
                                             scan_task_status, counter, keys_, 
                                             keys_g, keys_ge, keys_r, keys_d, 
                                             keys >>

clear_results(self) == ClearServiceRequest(self)

StatusServiceRequest(self) == /\ pc[self] = "StatusServiceRequest"
                              /\ \E key \in keys_ge[self]:
                                   /\ key_to_be_served' = key
                                   /\ service_request' = "status"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ keys_ge' = [keys_ge EXCEPT ![self] = Head(stack[self]).keys_ge]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, counter, keys_, 
                                              keys_g, keys_c, keys_r, keys_d, 
                                              keys >>

get_status(self) == StatusServiceRequest(self)

RegisterServiceRequest(self) == /\ pc[self] = "RegisterServiceRequest"
                                /\ \E key \in keys_r[self]:
                                     /\ key_to_be_served' = key
                                     /\ service_request' = "register"
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ keys_r' = [keys_r EXCEPT ![self] = Head(stack[self]).keys_r]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << scan_tasks, response, 
                                                scan_task_status, counter, 
                                                keys_, keys_g, keys_c, keys_ge, 
                                                keys_d, keys >>

register_keys(self) == RegisterServiceRequest(self)

DeleteServiceRequest(self) == /\ pc[self] = "DeleteServiceRequest"
                              /\ \E key \in keys_d[self]:
                                   /\ key_to_be_served' = key
                                   /\ service_request' = "delete"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ keys_d' = [keys_d EXCEPT ![self] = Head(stack[self]).keys_d]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, counter, keys_, 
                                              keys_g, keys_c, keys_ge, keys_r, 
                                              keys >>

delete_keys(self) == DeleteServiceRequest(self)

RegisterServiceRequestFromScan(self) == /\ pc[self] = "RegisterServiceRequestFromScan"
                                        /\ \E key \in keys[self]:
                                             /\ key_to_be_served' = key
                                             /\ service_request' = "register"
                                        /\ pc' = [pc EXCEPT ![self] = "ResultsServiceRequestFromScan"]
                                        /\ UNCHANGED << scan_tasks, response, 
                                                        scan_task_status, 
                                                        counter, stack, keys_, 
                                                        keys_g, keys_c, 
                                                        keys_ge, keys_r, 
                                                        keys_d, keys >>

ResultsServiceRequestFromScan(self) == /\ pc[self] = "ResultsServiceRequestFromScan"
                                       /\ \E key \in keys[self]:
                                            /\ key_to_be_served' = key
                                            /\ service_request' = "results"
                                       /\ pc' = [pc EXCEPT ![self] = "SubscribeServiceRequestFromScan"]
                                       /\ UNCHANGED << scan_tasks, response, 
                                                       scan_task_status, 
                                                       counter, stack, keys_, 
                                                       keys_g, keys_c, keys_ge, 
                                                       keys_r, keys_d, keys >>

SubscribeServiceRequestFromScan(self) == /\ pc[self] = "SubscribeServiceRequestFromScan"
                                         /\ \E key \in keys[self]:
                                              /\ key_to_be_served' = key
                                              /\ service_request' = "subscribe"
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ keys' = [keys EXCEPT ![self] = Head(stack[self]).keys]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED << scan_tasks, response, 
                                                         scan_task_status, 
                                                         counter, keys_, 
                                                         keys_g, keys_c, 
                                                         keys_ge, keys_r, 
                                                         keys_d >>

scan(self) == RegisterServiceRequestFromScan(self)
                 \/ ResultsServiceRequestFromScan(self)
                 \/ SubscribeServiceRequestFromScan(self)

Services == /\ pc["SERVICES"] = "Services"
            /\ IF service_request = "info"
                  THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Info"]
                       /\ UNCHANGED << response, scan_task_status >>
                  ELSE /\ IF service_request = "results"
                             THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Results"]
                                  /\ UNCHANGED << response, scan_task_status >>
                             ELSE /\ IF service_request = "clear"
                                        THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Clear"]
                                             /\ UNCHANGED << response, 
                                                             scan_task_status >>
                                        ELSE /\ IF service_request = "status"
                                                   THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Status"]
                                                        /\ UNCHANGED << response, 
                                                                        scan_task_status >>
                                                   ELSE /\ IF service_request = "register"
                                                              THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Register"]
                                                                   /\ UNCHANGED << response, 
                                                                                   scan_task_status >>
                                                              ELSE /\ IF service_request = "delete"
                                                                         THEN /\ IF key_to_be_served \in scan_tasks
                                                                                    THEN /\ scan_task_status' = "deleting"
                                                                                         /\ response' = delete_response
                                                                                    ELSE /\ response' = "Error: key not found."
                                                                                         /\ UNCHANGED scan_task_status
                                                                              /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
                                                                         ELSE /\ IF service_request = "subscribe"
                                                                                    THEN /\ pc' = [pc EXCEPT !["SERVICES"] = "Subscribe"]
                                                                                    ELSE /\ TRUE
                                                                                         /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
                                                                              /\ UNCHANGED << response, 
                                                                                              scan_task_status >>
            /\ UNCHANGED << scan_tasks, key_to_be_served, service_request, 
                            counter, stack, keys_, keys_g, keys_c, keys_ge, 
                            keys_r, keys_d, keys >>

Info == /\ pc["SERVICES"] = "Info"
        /\ response' = info_response
        /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
        /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                        service_request, counter, stack, keys_, keys_g, keys_c, 
                        keys_ge, keys_r, keys_d, keys >>

Results == /\ pc["SERVICES"] = "Results"
           /\ IF key_to_be_served \in scan_tasks
                 THEN /\ response' = results_response
                 ELSE /\ response' = "Error: key not found."
           /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
           /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                           service_request, counter, stack, keys_, keys_g, 
                           keys_c, keys_ge, keys_r, keys_d, keys >>

Clear == /\ pc["SERVICES"] = "Clear"
         /\ IF key_to_be_served \in scan_tasks
               THEN /\ response' = clear_response
               ELSE /\ response' = "Error: key not found."
         /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
         /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                         service_request, counter, stack, keys_, keys_g, 
                         keys_c, keys_ge, keys_r, keys_d, keys >>

Status == /\ pc["SERVICES"] = "Status"
          /\ IF key_to_be_served \in scan_tasks
                THEN /\ response' = status_response
                ELSE /\ response' = "Error: key not found."
          /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
          /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                          service_request, counter, stack, keys_, keys_g, 
                          keys_c, keys_ge, keys_r, keys_d, keys >>

Register == /\ pc["SERVICES"] = "Register"
            /\ IF key_to_be_served \in scan_tasks
                  THEN /\ response' = "Error: key already in scan task."
                       /\ UNCHANGED scan_task_status
                  ELSE /\ scan_task_status' = "adding"
                       /\ response' = register_response
            /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
            /\ UNCHANGED << scan_tasks, key_to_be_served, service_request, 
                            counter, stack, keys_, keys_g, keys_c, keys_ge, 
                            keys_r, keys_d, keys >>

Subscribe == /\ pc["SERVICES"] = "Subscribe"
             /\ IF key_to_be_served \in scan_tasks
                   THEN /\ response' = subscribe_response
                   ELSE /\ response' = "Error: key not found."
             /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
             /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                             service_request, counter, stack, keys_, keys_g, 
                             keys_c, keys_ge, keys_r, keys_d, keys >>

services == Services \/ Info \/ Results \/ Clear \/ Status \/ Register
               \/ Subscribe

AddTask == /\ pc["SCAN TASK"] = "AddTask"
           /\ IF scan_task_status = "adding"
                 THEN /\ scan_tasks' = (scan_tasks \union {key_to_be_served})
                      /\ scan_task_status' = "waiting"
                 ELSE /\ IF scan_task_status = "deleting"
                            THEN /\ scan_tasks' = scan_tasks \ {key_to_be_served}
                                 /\ scan_task_status' = "waiting"
                            ELSE /\ TRUE
                                 /\ UNCHANGED << scan_tasks, scan_task_status >>
           /\ pc' = [pc EXCEPT !["SCAN TASK"] = "Done"]
           /\ UNCHANGED << response, key_to_be_served, service_request, 
                           counter, stack, keys_, keys_g, keys_c, keys_ge, 
                           keys_r, keys_d, keys >>

scantask == AddTask

ConfigGuard == /\ pc["MAIN"] = "ConfigGuard"
               /\ IF ConfigViewingKeys # {}
                     THEN /\ pc' = [pc EXCEPT !["MAIN"] = "FromZebradConfig"]
                     ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_served, service_request, counter, 
                               stack, keys_, keys_g, keys_c, keys_ge, keys_r, 
                               keys_d, keys >>

FromZebradConfig == /\ pc["MAIN"] = "FromZebradConfig"
                    /\ \/ /\ /\ keys_' = [keys_ EXCEPT !["MAIN"] = ConfigViewingKeys]
                             /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "add_config_keys",
                                                                        pc        |->  "ListeningGuard",
                                                                        keys_     |->  keys_["MAIN"] ] >>
                                                                    \o stack["MAIN"]]
                          /\ pc' = [pc EXCEPT !["MAIN"] = "AddConfigKeys"]
                       \/ /\ TRUE
                          /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
                          /\ UNCHANGED <<stack, keys_>>
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, counter, 
                                    keys_g, keys_c, keys_ge, keys_r, keys_d, 
                                    keys >>

ListeningGuard == /\ pc["MAIN"] = "ListeningGuard"
                  /\ IF GrpcViewingKeys # <<>>
                        THEN /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningMode"]
                        ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, counter, 
                                  stack, keys_, keys_g, keys_c, keys_ge, 
                                  keys_r, keys_d, keys >>

ListeningMode == /\ pc["MAIN"] = "ListeningMode"
                 /\ IF counter <= Len(GrpcViewingKeys)
                       THEN /\ \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetInfoCall"]
                               \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetResultsCall"]
                               \/ /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterKeysCall"]
                               \/ /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteKeysCall"]
                               \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ClearResultsCall"]
                               \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ScanCall"]
                               \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetStatusCall"]
                       ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "End"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_served, service_request, counter, 
                                 stack, keys_, keys_g, keys_c, keys_ge, keys_r, 
                                 keys_d, keys >>

IncrementCounter == /\ pc["MAIN"] = "IncrementCounter"
                    /\ counter' = counter + 1
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningMode"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, stack, 
                                    keys_, keys_g, keys_c, keys_ge, keys_r, 
                                    keys_d, keys >>

GetInfoCall == /\ pc["MAIN"] = "GetInfoCall"
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_info",
                                                          pc        |->  "IncrementCounter" ] >>
                                                      \o stack["MAIN"]]
               /\ pc' = [pc EXCEPT !["MAIN"] = "InfoServiceRequest"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_served, service_request, counter, 
                               keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, 
                               keys >>

GetResultsCall == /\ pc["MAIN"] = "GetResultsCall"
                  /\ /\ keys_g' = [keys_g EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_results",
                                                                pc        |->  "IncrementCounter",
                                                                keys_g    |->  keys_g["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "ResultsServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, counter, 
                                  keys_, keys_c, keys_ge, keys_r, keys_d, keys >>

RegisterKeysCall == /\ pc["MAIN"] = "RegisterKeysCall"
                    /\ /\ keys_r' = [keys_r EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "register_keys",
                                                                  pc        |->  "IncrementCounter",
                                                                  keys_r    |->  keys_r["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, counter, 
                                    keys_, keys_g, keys_c, keys_ge, keys_d, 
                                    keys >>

DeleteKeysCall == /\ pc["MAIN"] = "DeleteKeysCall"
                  /\ /\ keys_d' = [keys_d EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "delete_keys",
                                                                pc        |->  "IncrementCounter",
                                                                keys_d    |->  keys_d["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, counter, 
                                  keys_, keys_g, keys_c, keys_ge, keys_r, keys >>

ClearResultsCall == /\ pc["MAIN"] = "ClearResultsCall"
                    /\ /\ keys_c' = [keys_c EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "clear_results",
                                                                  pc        |->  "IncrementCounter",
                                                                  keys_c    |->  keys_c["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ClearServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, counter, 
                                    keys_, keys_g, keys_ge, keys_r, keys_d, 
                                    keys >>

ScanCall == /\ pc["MAIN"] = "ScanCall"
            /\ /\ keys' = [keys EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "scan",
                                                          pc        |->  "IncrementCounter",
                                                          keys      |->  keys["MAIN"] ] >>
                                                      \o stack["MAIN"]]
            /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequestFromScan"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_served, service_request, counter, keys_, 
                            keys_g, keys_c, keys_ge, keys_r, keys_d >>

GetStatusCall == /\ pc["MAIN"] = "GetStatusCall"
                 /\ /\ keys_ge' = [keys_ge EXCEPT !["MAIN"] = GrpcViewingKeys[counter]]
                    /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_status",
                                                               pc        |->  "IncrementCounter",
                                                               keys_ge   |->  keys_ge["MAIN"] ] >>
                                                           \o stack["MAIN"]]
                 /\ pc' = [pc EXCEPT !["MAIN"] = "StatusServiceRequest"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_served, service_request, counter, 
                                 keys_, keys_g, keys_c, keys_r, keys_d, keys >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                       key_to_be_served, service_request, counter, stack, 
                       keys_, keys_g, keys_c, keys_ge, keys_r, keys_d, keys >>

Main == ConfigGuard \/ FromZebradConfig \/ ListeningGuard \/ ListeningMode
           \/ IncrementCounter \/ GetInfoCall \/ GetResultsCall
           \/ RegisterKeysCall \/ DeleteKeysCall \/ ClearResultsCall
           \/ ScanCall \/ GetStatusCall \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == services \/ scantask \/ Main
           \/ (\E self \in ProcSet:  \/ add_config_keys(self) \/ get_info(self)
                                     \/ get_results(self) \/ clear_results(self)
                                     \/ get_status(self) \/ register_keys(self)
                                     \/ delete_keys(self) \/ scan(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Mar 07 18:13:46 UYT 2024 by alfredo
\* Created Wed Feb 21 10:40:53 UYT 2024 by alfredo
