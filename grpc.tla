-------------------------------- MODULE grpc --------------------------------
EXTENDS TLC, Integers, Sequences, Randomization

\* CONFIGURATION CONSTANTS:

\* Key as string to be added to the scan task from the config file.
CONSTANT ConfigViewingKey
\* Key as string to be added to the scan task by calling grpc methods.
CONSTANT GrpcViewingKey

\* GLOBAL VARIABLES:

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

\* The type invariants.
define
  TypeInvariant ==
    /\ response \in STRING
    /\ scan_task_status \in scan_task_statuses
    /\ key_to_be_served \in STRING
    /\ service_request \in service_requests
end define;

\* Call the scan task to add keys coming from the config file.
procedure add_config_keys(key)
begin
    AddConfigKeys:
        key_to_be_served := key;
        scan_task_status := "adding";
        return;
end procedure;

\* The `get_info` grpc method.
procedure get_info()
begin
    InfoServiceRequest:
        service_request := "info";
        return;
end procedure;

\* The `get_results` grpc method.
procedure get_results(key)
begin
    ResultsServiceRequest:
        key_to_be_served := key;
        service_request := "results";
        return;
end procedure;

\* The `clear_results` grpc method.
procedure clear_results(key)
begin
    ClearServiceRequest:
        key_to_be_served := key;
        service_request := "clear";
        return;
end procedure;

\* The `get_status` grpc method.
procedure get_status(key)
begin
    StatusServiceRequest:
        key_to_be_served := key;
        service_request := "status";
        return;
end procedure;

\* The `register_keys` grpc method.
procedure register_keys(key)
begin
    RegisterServiceRequest:
        key_to_be_served := key;
        service_request := "register";
        return;
end procedure;

\* The `delete_keys` grpc method.
procedure delete_keys(key)
begin
    DeleteServiceRequest:
        key_to_be_served := key;
        service_request := "delete";
        return;
end procedure;

\* The `scan` grpc method.
procedure scan(key)
begin
    RegisterServiceRequestFromScan:
        key_to_be_served := key;
        service_request := "register";
    ResultsServiceRequestFromScan:
        service_request := "results";
    SubscribeServiceRequestFromScan:
        service_request := "subscribe";
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
        if ConfigViewingKey # "" then
            FromZebradConfig:
                either call add_config_keys(ConfigViewingKey); or skip; end either;
        end if;
    ListeningGuard:
        if GrpcViewingKey # "" then
            ListeningMode:
                either GetInfoCall:
                    call get_info();
                or GetResultsCall:
                    call get_results(GrpcViewingKey);
                or RegisterKeysCall:
                    call register_keys(GrpcViewingKey);
                or DeleteKeysCall:
                    call delete_keys(GrpcViewingKey);
                or ClearResultsCall:
                    call clear_results(GrpcViewingKey);
                or ScanCall:
                    call scan(GrpcViewingKey);
                or GetStatusCall:
                    call get_status(GrpcViewingKey);
                end either;
            End:
                skip;
        end if;
        
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8b2aa5fd" /\ chksum(tla) = "3263055")
\* Parameter key of procedure add_config_keys at line 56 col 27 changed to key_
\* Parameter key of procedure get_results at line 73 col 23 changed to key_g
\* Parameter key of procedure clear_results at line 82 col 25 changed to key_c
\* Parameter key of procedure get_status at line 91 col 22 changed to key_ge
\* Parameter key of procedure register_keys at line 100 col 25 changed to key_r
\* Parameter key of procedure delete_keys at line 109 col 23 changed to key_d
CONSTANT defaultInitValue
VARIABLES scan_tasks, response, scan_task_status, key_to_be_served, 
          service_request, pc, stack

(* define statement *)
TypeInvariant ==
  /\ response \in STRING
  /\ scan_task_status \in scan_task_statuses
  /\ key_to_be_served \in STRING
  /\ service_request \in service_requests

VARIABLES key_, key_g, key_c, key_ge, key_r, key_d, key

vars == << scan_tasks, response, scan_task_status, key_to_be_served, 
           service_request, pc, stack, key_, key_g, key_c, key_ge, key_r, 
           key_d, key >>

ProcSet == {"SERVICES"} \cup {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ scan_tasks = {}
        /\ response = ""
        /\ scan_task_status = "waiting"
        /\ key_to_be_served = ""
        /\ service_request = "none"
        (* Procedure add_config_keys *)
        /\ key_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_results *)
        /\ key_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure clear_results *)
        /\ key_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_status *)
        /\ key_ge = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure register_keys *)
        /\ key_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure delete_keys *)
        /\ key_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure scan *)
        /\ key = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "SERVICES" -> "Services"
                                        [] self = "SCAN TASK" -> "AddTask"
                                        [] self = "MAIN" -> "ConfigGuard"]

AddConfigKeys(self) == /\ pc[self] = "AddConfigKeys"
                       /\ key_to_be_served' = key_[self]
                       /\ scan_task_status' = "adding"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ key_' = [key_ EXCEPT ![self] = Head(stack[self]).key_]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << scan_tasks, response, service_request, 
                                       key_g, key_c, key_ge, key_r, key_d, key >>

add_config_keys(self) == AddConfigKeys(self)

InfoServiceRequest(self) == /\ pc[self] = "InfoServiceRequest"
                            /\ service_request' = "info"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << scan_tasks, response, 
                                            scan_task_status, key_to_be_served, 
                                            key_, key_g, key_c, key_ge, key_r, 
                                            key_d, key >>

get_info(self) == InfoServiceRequest(self)

ResultsServiceRequest(self) == /\ pc[self] = "ResultsServiceRequest"
                               /\ key_to_be_served' = key_g[self]
                               /\ service_request' = "results"
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ key_g' = [key_g EXCEPT ![self] = Head(stack[self]).key_g]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << scan_tasks, response, 
                                               scan_task_status, key_, key_c, 
                                               key_ge, key_r, key_d, key >>

get_results(self) == ResultsServiceRequest(self)

ClearServiceRequest(self) == /\ pc[self] = "ClearServiceRequest"
                             /\ key_to_be_served' = key_c[self]
                             /\ service_request' = "clear"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ key_c' = [key_c EXCEPT ![self] = Head(stack[self]).key_c]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << scan_tasks, response, 
                                             scan_task_status, key_, key_g, 
                                             key_ge, key_r, key_d, key >>

clear_results(self) == ClearServiceRequest(self)

StatusServiceRequest(self) == /\ pc[self] = "StatusServiceRequest"
                              /\ key_to_be_served' = key_ge[self]
                              /\ service_request' = "status"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ key_ge' = [key_ge EXCEPT ![self] = Head(stack[self]).key_ge]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, key_, key_g, 
                                              key_c, key_r, key_d, key >>

get_status(self) == StatusServiceRequest(self)

RegisterServiceRequest(self) == /\ pc[self] = "RegisterServiceRequest"
                                /\ key_to_be_served' = key_r[self]
                                /\ service_request' = "register"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ key_r' = [key_r EXCEPT ![self] = Head(stack[self]).key_r]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << scan_tasks, response, 
                                                scan_task_status, key_, key_g, 
                                                key_c, key_ge, key_d, key >>

register_keys(self) == RegisterServiceRequest(self)

DeleteServiceRequest(self) == /\ pc[self] = "DeleteServiceRequest"
                              /\ key_to_be_served' = key_d[self]
                              /\ service_request' = "delete"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ key_d' = [key_d EXCEPT ![self] = Head(stack[self]).key_d]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, key_, key_g, 
                                              key_c, key_ge, key_r, key >>

delete_keys(self) == DeleteServiceRequest(self)

RegisterServiceRequestFromScan(self) == /\ pc[self] = "RegisterServiceRequestFromScan"
                                        /\ key_to_be_served' = key[self]
                                        /\ service_request' = "register"
                                        /\ pc' = [pc EXCEPT ![self] = "ResultsServiceRequestFromScan"]
                                        /\ UNCHANGED << scan_tasks, response, 
                                                        scan_task_status, 
                                                        stack, key_, key_g, 
                                                        key_c, key_ge, key_r, 
                                                        key_d, key >>

ResultsServiceRequestFromScan(self) == /\ pc[self] = "ResultsServiceRequestFromScan"
                                       /\ service_request' = "results"
                                       /\ pc' = [pc EXCEPT ![self] = "SubscribeServiceRequestFromScan"]
                                       /\ UNCHANGED << scan_tasks, response, 
                                                       scan_task_status, 
                                                       key_to_be_served, stack, 
                                                       key_, key_g, key_c, 
                                                       key_ge, key_r, key_d, 
                                                       key >>

SubscribeServiceRequestFromScan(self) == /\ pc[self] = "SubscribeServiceRequestFromScan"
                                         /\ service_request' = "subscribe"
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ key' = [key EXCEPT ![self] = Head(stack[self]).key]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED << scan_tasks, response, 
                                                         scan_task_status, 
                                                         key_to_be_served, 
                                                         key_, key_g, key_c, 
                                                         key_ge, key_r, key_d >>

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
                            stack, key_, key_g, key_c, key_ge, key_r, key_d, 
                            key >>

Info == /\ pc["SERVICES"] = "Info"
        /\ response' = info_response
        /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
        /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                        service_request, stack, key_, key_g, key_c, key_ge, 
                        key_r, key_d, key >>

Results == /\ pc["SERVICES"] = "Results"
           /\ IF key_to_be_served \in scan_tasks
                 THEN /\ response' = results_response
                 ELSE /\ response' = "Error: key not found."
           /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
           /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                           service_request, stack, key_, key_g, key_c, key_ge, 
                           key_r, key_d, key >>

Clear == /\ pc["SERVICES"] = "Clear"
         /\ IF key_to_be_served \in scan_tasks
               THEN /\ response' = clear_response
               ELSE /\ response' = "Error: key not found."
         /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
         /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                         service_request, stack, key_, key_g, key_c, key_ge, 
                         key_r, key_d, key >>

Status == /\ pc["SERVICES"] = "Status"
          /\ IF key_to_be_served \in scan_tasks
                THEN /\ response' = status_response
                ELSE /\ response' = "Error: key not found."
          /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
          /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                          service_request, stack, key_, key_g, key_c, key_ge, 
                          key_r, key_d, key >>

Register == /\ pc["SERVICES"] = "Register"
            /\ IF key_to_be_served \in scan_tasks
                  THEN /\ response' = "Error: key already in scan task."
                       /\ UNCHANGED scan_task_status
                  ELSE /\ scan_task_status' = "adding"
                       /\ response' = register_response
            /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
            /\ UNCHANGED << scan_tasks, key_to_be_served, service_request, 
                            stack, key_, key_g, key_c, key_ge, key_r, key_d, 
                            key >>

Subscribe == /\ pc["SERVICES"] = "Subscribe"
             /\ IF key_to_be_served \in scan_tasks
                   THEN /\ response' = subscribe_response
                   ELSE /\ response' = "Error: key not found."
             /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
             /\ UNCHANGED << scan_tasks, scan_task_status, key_to_be_served, 
                             service_request, stack, key_, key_g, key_c, 
                             key_ge, key_r, key_d, key >>

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
           /\ UNCHANGED << response, key_to_be_served, service_request, stack, 
                           key_, key_g, key_c, key_ge, key_r, key_d, key >>

scantask == AddTask

ConfigGuard == /\ pc["MAIN"] = "ConfigGuard"
               /\ IF ConfigViewingKey # ""
                     THEN /\ pc' = [pc EXCEPT !["MAIN"] = "FromZebradConfig"]
                     ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_served, service_request, stack, key_, 
                               key_g, key_c, key_ge, key_r, key_d, key >>

FromZebradConfig == /\ pc["MAIN"] = "FromZebradConfig"
                    /\ \/ /\ /\ key_' = [key_ EXCEPT !["MAIN"] = ConfigViewingKey]
                             /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "add_config_keys",
                                                                        pc        |->  "ListeningGuard",
                                                                        key_      |->  key_["MAIN"] ] >>
                                                                    \o stack["MAIN"]]
                          /\ pc' = [pc EXCEPT !["MAIN"] = "AddConfigKeys"]
                       \/ /\ TRUE
                          /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
                          /\ UNCHANGED <<stack, key_>>
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, key_g, 
                                    key_c, key_ge, key_r, key_d, key >>

ListeningGuard == /\ pc["MAIN"] = "ListeningGuard"
                  /\ IF GrpcViewingKey # ""
                        THEN /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningMode"]
                        ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, stack, 
                                  key_, key_g, key_c, key_ge, key_r, key_d, 
                                  key >>

ListeningMode == /\ pc["MAIN"] = "ListeningMode"
                 /\ \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetInfoCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetResultsCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterKeysCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteKeysCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ClearResultsCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ScanCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetStatusCall"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_served, service_request, stack, 
                                 key_, key_g, key_c, key_ge, key_r, key_d, key >>

GetInfoCall == /\ pc["MAIN"] = "GetInfoCall"
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_info",
                                                          pc        |->  "End" ] >>
                                                      \o stack["MAIN"]]
               /\ pc' = [pc EXCEPT !["MAIN"] = "InfoServiceRequest"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_served, service_request, key_, key_g, 
                               key_c, key_ge, key_r, key_d, key >>

GetResultsCall == /\ pc["MAIN"] = "GetResultsCall"
                  /\ /\ key_g' = [key_g EXCEPT !["MAIN"] = GrpcViewingKey]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_results",
                                                                pc        |->  "End",
                                                                key_g     |->  key_g["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "ResultsServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, key_, 
                                  key_c, key_ge, key_r, key_d, key >>

RegisterKeysCall == /\ pc["MAIN"] = "RegisterKeysCall"
                    /\ /\ key_r' = [key_r EXCEPT !["MAIN"] = GrpcViewingKey]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "register_keys",
                                                                  pc        |->  "End",
                                                                  key_r     |->  key_r["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, key_, 
                                    key_g, key_c, key_ge, key_d, key >>

DeleteKeysCall == /\ pc["MAIN"] = "DeleteKeysCall"
                  /\ /\ key_d' = [key_d EXCEPT !["MAIN"] = GrpcViewingKey]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "delete_keys",
                                                                pc        |->  "End",
                                                                key_d     |->  key_d["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_served, service_request, key_, 
                                  key_g, key_c, key_ge, key_r, key >>

ClearResultsCall == /\ pc["MAIN"] = "ClearResultsCall"
                    /\ /\ key_c' = [key_c EXCEPT !["MAIN"] = GrpcViewingKey]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "clear_results",
                                                                  pc        |->  "End",
                                                                  key_c     |->  key_c["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ClearServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_served, service_request, key_, 
                                    key_g, key_ge, key_r, key_d, key >>

ScanCall == /\ pc["MAIN"] = "ScanCall"
            /\ /\ key' = [key EXCEPT !["MAIN"] = GrpcViewingKey]
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "scan",
                                                          pc        |->  "End",
                                                          key       |->  key["MAIN"] ] >>
                                                      \o stack["MAIN"]]
            /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequestFromScan"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_served, service_request, key_, key_g, 
                            key_c, key_ge, key_r, key_d >>

GetStatusCall == /\ pc["MAIN"] = "GetStatusCall"
                 /\ /\ key_ge' = [key_ge EXCEPT !["MAIN"] = GrpcViewingKey]
                    /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_status",
                                                               pc        |->  "End",
                                                               key_ge    |->  key_ge["MAIN"] ] >>
                                                           \o stack["MAIN"]]
                 /\ pc' = [pc EXCEPT !["MAIN"] = "StatusServiceRequest"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_served, service_request, key_, 
                                 key_g, key_c, key_r, key_d, key >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                       key_to_be_served, service_request, stack, key_, key_g, 
                       key_c, key_ge, key_r, key_d, key >>

Main == ConfigGuard \/ FromZebradConfig \/ ListeningGuard \/ ListeningMode
           \/ GetInfoCall \/ GetResultsCall \/ RegisterKeysCall
           \/ DeleteKeysCall \/ ClearResultsCall \/ ScanCall
           \/ GetStatusCall \/ End

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
\* Last modified Wed Mar 06 13:53:24 UYT 2024 by alfredo
\* Created Wed Feb 21 10:40:53 UYT 2024 by alfredo
