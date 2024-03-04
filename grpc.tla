-------------------------------- MODULE grpc --------------------------------
EXTENDS TLC, Integers, Sequences, Randomization

CONSTANT ConfigViewingKey \* Sequence of keys to be added to the scan task from the config file.
CONSTANT GrpcViewingKey \* Sequence of keys to be added to the scan task by calling grpc methods.

info_response == [saplingheight |-> 1] \* A fixed response to an `Info` request
results_response == [transactions |-> RandomSetOfSubsets(1, 3, 1..10)] \* A random list of transations to be used as a `Results` response.
register_response == [empty |-> {}] \* A fixed response to `Register`.
delete_response == [empty |-> {}] \* A fixed response to `Delete`.
clear_response == [empty |-> {}] \* A fixed response to `Clear`.
subscribe_response == [empty |-> {}] \* A fixed response to `Subscribe`. TODO: which should be a channel with updates.
status_response == [empty |-> {}] \* A fixed response to `Status`. TODO: which should have some data from the scan task for the key.

scan_task_statuses == {"waiting", "adding", "deleting"} \* The set of statuses a scan task can be on at any given time.

(*--algorithm grpc
variables
    scan_tasks = {}; \* The scan tasks are a set that is initially empty
    response = ""; \* A string that will be used as a response to any of the gRPC method calls
    scan_task_status = "waiting"; \* The status of the scan task, initially listening
    key_to_be_added_or_deleted = ""; \* The key to be added or deleted to/from the scan task at a given instant, initially empty.
    
    service_request = "none"; \* The current service request flag.
define
  TypeInvariant ==
    /\ response \in STRING
    /\ scan_task_status \in scan_task_statuses
    /\ key_to_be_added_or_deleted \in STRING
end define;


\* Call the scan task to add keys coming from the config file.
procedure add_config_keys(key)
begin
    AddConfigKeys:
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
        service_request := "results";
        return;
end procedure;

\* The `clear_results` grpc method.
procedure clear_results(key)
begin
    ClearServiceRequest:
        service_request := "clear";
        return;
end procedure;

\* The `get_status` grpc method.
procedure get_status()
begin
    StatusServiceRequest:
        service_request := "status";
        return;
end procedure;

\* The `register_keys` grpc method.
procedure register_keys(key)
begin
    RegisterServiceRequest:
        service_request := "register";
        return;
end procedure;

\* The `delete_keys` grpc method.
procedure delete_keys(key)
begin
    DeleteServiceRequest:
        service_request := "delete";
        return;
end procedure;

\* The `scan` grpc method.
procedure scan(key)
begin
    RegisterServiceRequest:
        service_request := "register";
        return;
    ResultsServiceRequest:
        service_request := "results";
    subscribeServiceRequest:
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
            if key \in scan_tasks then
                response := results_response;
            else
                response := "error";
            end if;
    elsif service_request = "clear" then
        Clear:
            response := clear_response;
    elsif service_request = "status" then
        Status:
            response := clear_response;
    elsif service_request = "register" then
        Register:
            key_to_be_added_or_deleted := key;
            scan_task_status := "adding";
            response := register_response;
    elsif service_request = "delete" then
        Delete:
            key_to_be_added_or_deleted := key;
            scan_task_status := "deleting";
            response := delete_response;
    elsif service_request = "subscribe" then
        Subscribe:
            response := subscribe_response;
    else 
        skip;
    end if;
end process;


\* The scan task process, in charge of adding and removing tasks to the scan task set.
process scantask = "SCAN TASK"
begin
  AddTask:
    if scan_task_status = "adding" then
        await scan_tasks = {};
        scan_tasks := scan_tasks \union {key_to_be_added_or_deleted};
        scan_task_status := "waiting";
    elsif scan_task_status = "deleting" then
        \*await scan_tasks # <<>>;
        scan_tasks := scan_tasks \ {key_to_be_added_or_deleted};
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
                end either;
            End:
                skip;
        end if;
        
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "cd4901ca" /\ chksum(tla) = "ba4b2834")
\* Label ResultsServiceRequest of procedure get_results at line 53 col 9 changed to ResultsServiceRequest_
\* Label RegisterServiceRequest of procedure register_keys at line 77 col 9 changed to RegisterServiceRequest_
\* Parameter key of procedure add_config_keys at line 34 col 27 changed to key_
\* Parameter key of procedure get_results at line 50 col 23 changed to key_g
\* Parameter key of procedure clear_results at line 58 col 25 changed to key_c
\* Parameter key of procedure register_keys at line 74 col 25 changed to key_r
\* Parameter key of procedure delete_keys at line 82 col 23 changed to key_d
CONSTANT defaultInitValue
VARIABLES scan_tasks, response, scan_task_status, key_to_be_added_or_deleted, 
          service_request, pc, stack

(* define statement *)
TypeInvariant ==
  /\ response \in STRING
  /\ scan_task_status \in scan_task_statuses
  /\ key_to_be_added_or_deleted \in STRING

VARIABLES key_, key_g, key_c, key_r, key_d, key

vars == << scan_tasks, response, scan_task_status, key_to_be_added_or_deleted, 
           service_request, pc, stack, key_, key_g, key_c, key_r, key_d, key
        >>

ProcSet == {"SERVICES"} \cup {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ scan_tasks = {}
        /\ response = ""
        /\ scan_task_status = "waiting"
        /\ key_to_be_added_or_deleted = ""
        /\ service_request = "none"
        (* Procedure add_config_keys *)
        /\ key_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_results *)
        /\ key_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure clear_results *)
        /\ key_c = [ self \in ProcSet |-> defaultInitValue]
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
                       /\ scan_task_status' = "adding"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ key_' = [key_ EXCEPT ![self] = Head(stack[self]).key_]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << scan_tasks, response, 
                                       key_to_be_added_or_deleted, 
                                       service_request, key_g, key_c, key_r, 
                                       key_d, key >>

add_config_keys(self) == AddConfigKeys(self)

InfoServiceRequest(self) == /\ pc[self] = "InfoServiceRequest"
                            /\ service_request' = "info"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << scan_tasks, response, 
                                            scan_task_status, 
                                            key_to_be_added_or_deleted, key_, 
                                            key_g, key_c, key_r, key_d, key >>

get_info(self) == InfoServiceRequest(self)

ResultsServiceRequest_(self) == /\ pc[self] = "ResultsServiceRequest_"
                                /\ service_request' = "results"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ key_g' = [key_g EXCEPT ![self] = Head(stack[self]).key_g]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << scan_tasks, response, 
                                                scan_task_status, 
                                                key_to_be_added_or_deleted, 
                                                key_, key_c, key_r, key_d, key >>

get_results(self) == ResultsServiceRequest_(self)

ClearServiceRequest(self) == /\ pc[self] = "ClearServiceRequest"
                             /\ service_request' = "clear"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ key_c' = [key_c EXCEPT ![self] = Head(stack[self]).key_c]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << scan_tasks, response, 
                                             scan_task_status, 
                                             key_to_be_added_or_deleted, key_, 
                                             key_g, key_r, key_d, key >>

clear_results(self) == ClearServiceRequest(self)

StatusServiceRequest(self) == /\ pc[self] = "StatusServiceRequest"
                              /\ service_request' = "status"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, 
                                              key_to_be_added_or_deleted, key_, 
                                              key_g, key_c, key_r, key_d, key >>

get_status(self) == StatusServiceRequest(self)

RegisterServiceRequest_(self) == /\ pc[self] = "RegisterServiceRequest_"
                                 /\ service_request' = "register"
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ key_r' = [key_r EXCEPT ![self] = Head(stack[self]).key_r]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << scan_tasks, response, 
                                                 scan_task_status, 
                                                 key_to_be_added_or_deleted, 
                                                 key_, key_g, key_c, key_d, 
                                                 key >>

register_keys(self) == RegisterServiceRequest_(self)

DeleteServiceRequest(self) == /\ pc[self] = "DeleteServiceRequest"
                              /\ service_request' = "delete"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ key_d' = [key_d EXCEPT ![self] = Head(stack[self]).key_d]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << scan_tasks, response, 
                                              scan_task_status, 
                                              key_to_be_added_or_deleted, key_, 
                                              key_g, key_c, key_r, key >>

delete_keys(self) == DeleteServiceRequest(self)

RegisterServiceRequest(self) == /\ pc[self] = "RegisterServiceRequest"
                                /\ service_request' = "register"
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ key' = [key EXCEPT ![self] = Head(stack[self]).key]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << scan_tasks, response, 
                                                scan_task_status, 
                                                key_to_be_added_or_deleted, 
                                                key_, key_g, key_c, key_r, 
                                                key_d >>

ResultsServiceRequest(self) == /\ pc[self] = "ResultsServiceRequest"
                               /\ service_request' = "results"
                               /\ pc' = [pc EXCEPT ![self] = "subscribeServiceRequest"]
                               /\ UNCHANGED << scan_tasks, response, 
                                               scan_task_status, 
                                               key_to_be_added_or_deleted, 
                                               stack, key_, key_g, key_c, 
                                               key_r, key_d, key >>

subscribeServiceRequest(self) == /\ pc[self] = "subscribeServiceRequest"
                                 /\ service_request' = "subscribe"
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ key' = [key EXCEPT ![self] = Head(stack[self]).key]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << scan_tasks, response, 
                                                 scan_task_status, 
                                                 key_to_be_added_or_deleted, 
                                                 key_, key_g, key_c, key_r, 
                                                 key_d >>

scan(self) == RegisterServiceRequest(self) \/ ResultsServiceRequest(self)
                 \/ subscribeServiceRequest(self)

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
                                                                                    ELSE /\ TRUE
                                                                                         /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_added_or_deleted, service_request, stack, 
                            key_, key_g, key_c, key_r, key_d, key >>

Info == /\ pc["SERVICES"] = "Info"
        /\ response' = info_response
        /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
        /\ UNCHANGED << scan_tasks, scan_task_status, 
                        key_to_be_added_or_deleted, service_request, stack, 
                        key_, key_g, key_c, key_r, key_d, key >>

Results == /\ pc["SERVICES"] = "Results"
           /\ IF key["SERVICES"] \in scan_tasks
                 THEN /\ response' = results_response
                 ELSE /\ response' = "error"
           /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
           /\ UNCHANGED << scan_tasks, scan_task_status, 
                           key_to_be_added_or_deleted, service_request, stack, 
                           key_, key_g, key_c, key_r, key_d, key >>

Clear == /\ pc["SERVICES"] = "Clear"
         /\ response' = clear_response
         /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
         /\ UNCHANGED << scan_tasks, scan_task_status, 
                         key_to_be_added_or_deleted, service_request, stack, 
                         key_, key_g, key_c, key_r, key_d, key >>

Status == /\ pc["SERVICES"] = "Status"
          /\ response' = clear_response
          /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
          /\ UNCHANGED << scan_tasks, scan_task_status, 
                          key_to_be_added_or_deleted, service_request, stack, 
                          key_, key_g, key_c, key_r, key_d, key >>

Register == /\ pc["SERVICES"] = "Register"
            /\ key_to_be_added_or_deleted' = key["SERVICES"]
            /\ scan_task_status' = "adding"
            /\ response' = register_response
            /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
            /\ UNCHANGED << scan_tasks, service_request, stack, key_, key_g, 
                            key_c, key_r, key_d, key >>

Delete == /\ pc["SERVICES"] = "Delete"
          /\ key_to_be_added_or_deleted' = key["SERVICES"]
          /\ scan_task_status' = "deleting"
          /\ response' = delete_response
          /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
          /\ UNCHANGED << scan_tasks, service_request, stack, key_, key_g, 
                          key_c, key_r, key_d, key >>

Subscribe == /\ pc["SERVICES"] = "Subscribe"
             /\ response' = subscribe_response
             /\ pc' = [pc EXCEPT !["SERVICES"] = "Done"]
             /\ UNCHANGED << scan_tasks, scan_task_status, 
                             key_to_be_added_or_deleted, service_request, 
                             stack, key_, key_g, key_c, key_r, key_d, key >>

services == Services \/ Info \/ Results \/ Clear \/ Status \/ Register
               \/ Delete \/ Subscribe

AddTask == /\ pc["SCAN TASK"] = "AddTask"
           /\ IF scan_task_status = "adding"
                 THEN /\ scan_tasks = {}
                      /\ scan_tasks' = (scan_tasks \union {key_to_be_added_or_deleted})
                      /\ scan_task_status' = "waiting"
                 ELSE /\ IF scan_task_status = "deleting"
                            THEN /\ scan_tasks' = scan_tasks \ {key_to_be_added_or_deleted}
                                 /\ scan_task_status' = "waiting"
                            ELSE /\ TRUE
                                 /\ UNCHANGED << scan_tasks, scan_task_status >>
           /\ pc' = [pc EXCEPT !["SCAN TASK"] = "Done"]
           /\ UNCHANGED << response, key_to_be_added_or_deleted, 
                           service_request, stack, key_, key_g, key_c, key_r, 
                           key_d, key >>

scantask == AddTask

ConfigGuard == /\ pc["MAIN"] = "ConfigGuard"
               /\ IF ConfigViewingKey # ""
                     THEN /\ pc' = [pc EXCEPT !["MAIN"] = "FromZebradConfig"]
                     ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_added_or_deleted, service_request, 
                               stack, key_, key_g, key_c, key_r, key_d, key >>

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
                                    key_to_be_added_or_deleted, 
                                    service_request, key_g, key_c, key_r, 
                                    key_d, key >>

ListeningGuard == /\ pc["MAIN"] = "ListeningGuard"
                  /\ IF GrpcViewingKey # ""
                        THEN /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningMode"]
                        ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_added_or_deleted, service_request, 
                                  stack, key_, key_g, key_c, key_r, key_d, key >>

ListeningMode == /\ pc["MAIN"] = "ListeningMode"
                 /\ \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetInfoCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetResultsCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterKeysCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteKeysCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ClearResultsCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ScanCall"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_added_or_deleted, service_request, 
                                 stack, key_, key_g, key_c, key_r, key_d, key >>

GetInfoCall == /\ pc["MAIN"] = "GetInfoCall"
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_info",
                                                          pc        |->  "End" ] >>
                                                      \o stack["MAIN"]]
               /\ pc' = [pc EXCEPT !["MAIN"] = "InfoServiceRequest"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_added_or_deleted, service_request, 
                               key_, key_g, key_c, key_r, key_d, key >>

GetResultsCall == /\ pc["MAIN"] = "GetResultsCall"
                  /\ /\ key_g' = [key_g EXCEPT !["MAIN"] = GrpcViewingKey]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_results",
                                                                pc        |->  "End",
                                                                key_g     |->  key_g["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "ResultsServiceRequest_"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_added_or_deleted, service_request, 
                                  key_, key_c, key_r, key_d, key >>

RegisterKeysCall == /\ pc["MAIN"] = "RegisterKeysCall"
                    /\ /\ key_r' = [key_r EXCEPT !["MAIN"] = GrpcViewingKey]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "register_keys",
                                                                  pc        |->  "End",
                                                                  key_r     |->  key_r["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequest_"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_added_or_deleted, 
                                    service_request, key_, key_g, key_c, key_d, 
                                    key >>

DeleteKeysCall == /\ pc["MAIN"] = "DeleteKeysCall"
                  /\ /\ key_d' = [key_d EXCEPT !["MAIN"] = GrpcViewingKey]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "delete_keys",
                                                                pc        |->  "End",
                                                                key_d     |->  key_d["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteServiceRequest"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_added_or_deleted, service_request, 
                                  key_, key_g, key_c, key_r, key >>

ClearResultsCall == /\ pc["MAIN"] = "ClearResultsCall"
                    /\ /\ key_c' = [key_c EXCEPT !["MAIN"] = GrpcViewingKey]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "clear_results",
                                                                  pc        |->  "End",
                                                                  key_c     |->  key_c["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ClearServiceRequest"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_added_or_deleted, 
                                    service_request, key_, key_g, key_r, key_d, 
                                    key >>

ScanCall == /\ pc["MAIN"] = "ScanCall"
            /\ /\ key' = [key EXCEPT !["MAIN"] = GrpcViewingKey]
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "scan",
                                                          pc        |->  "End",
                                                          key       |->  key["MAIN"] ] >>
                                                      \o stack["MAIN"]]
            /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterServiceRequest"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_added_or_deleted, service_request, key_, 
                            key_g, key_c, key_r, key_d >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                       key_to_be_added_or_deleted, service_request, stack, 
                       key_, key_g, key_c, key_r, key_d, key >>

Main == ConfigGuard \/ FromZebradConfig \/ ListeningGuard \/ ListeningMode
           \/ GetInfoCall \/ GetResultsCall \/ RegisterKeysCall
           \/ DeleteKeysCall \/ ClearResultsCall \/ ScanCall \/ End

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
\* Last modified Mon Mar 04 16:31:12 UYT 2024 by alfredo
\* Created Wed Feb 21 10:40:53 UYT 2024 by alfredo
