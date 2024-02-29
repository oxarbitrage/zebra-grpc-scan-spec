-------------------------------- MODULE grpc --------------------------------
EXTENDS TLC, Integers, Sequences, Json, Randomization

CONSTANT ConfigViewingKey \* Sequence of keys to be added to the scan task from the config file.
CONSTANT GrpcViewingKey \* Sequence of keys to be added to the scan task by calling grpc methods.

info_response == [saplingheight |-> 1] \* A fixed response to an `Info` request
results_response == [transactions |-> RandomSetOfSubsets(1, 3, 1..10)] \* A random list of transations to be used as a `Results` response.
register_response == [empty |-> {}] \* A fixed response to `Register`.
delete_response == [empty |-> {}] \* A fixed response to `Delete`.
clear_response == [empty |-> {}] \* A fixed response to `Clear`.
subscribe_response == [empty |-> {}] \* A fixed response to `Subscribe`. TODO: which should be a channel with updates.

scan_task_statuses == {"waiting", "adding", "deleting"} \* The set of statuses a scan task can be on at any given time.

(*--algorithm grpc
variables
    scan_tasks = {}; \* The scan tasks are a set that is initially empty
    response = ""; \* A string that will be used as a response to any of the gRPC method calls
    scan_task_status = "waiting"; \* The status of the scan task, initially listening
    
    key_to_be_added_or_deleted = ""; \* The key to be added or deleted to/from the scan task at a given instant, initially empty.
    
define
  TypeInvariant ==
    /\ response \in STRING
    /\ scan_task_status \in scan_task_statuses 
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
    InfoService:
        response := ToJson(info_response);
        return;
end procedure;

\* The `get_results` grpc method.
procedure get_results(key)
begin
    ResultsService:
        if key \in scan_tasks then
            response := ToJson(results_response);
        else
            response := ToJson("error");
        end if;
    return;
end procedure;

\* The `register_keys` grpc method.
procedure register_keys(key)
begin
    RegisterService:
        key_to_be_added_or_deleted := key;
        scan_task_status := "adding";
        response := ToJson(register_response);
        return;
end procedure;

\* The `delete_keys` grpc method.
procedure delete_keys(key)
begin
    DeleteService:
        key_to_be_added_or_deleted := key;
        scan_task_status := "deleting";
        response := ToJson(delete_response);
        return;
end procedure;

\* The `clear_results` grpc method.
procedure clear_results(key)
begin
    ClearService:
        response := ToJson(clear_response);
        return;
end procedure;

\* The `Subscribe` service.
procedure subscribe(key)
begin
    SubscribeService:
        response := ToJson(subscribe_response);
        return;
end procedure;

\* The `scan` grpc method.
procedure scan(key)
begin
    ScanService:
        goto ScanRegister;
    ScanRegister:
        call register_keys(key);
        goto ScanResults;
    ScanResults:
        call get_results(key);
        goto ScanSubscribe;
    ScanSubscribe:
        call subscribe(key);
        return;
end procedure;

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
process MainLoop = "MAIN"
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
\* BEGIN TRANSLATION (chksum(pcal) = "57788cf3" /\ chksum(tla) = "970d6406")
\* Parameter key of procedure add_config_keys at line 31 col 27 changed to key_
\* Parameter key of procedure get_results at line 47 col 23 changed to key_g
\* Parameter key of procedure register_keys at line 59 col 25 changed to key_r
\* Parameter key of procedure delete_keys at line 69 col 23 changed to key_d
\* Parameter key of procedure clear_results at line 79 col 25 changed to key_c
\* Parameter key of procedure subscribe at line 87 col 21 changed to key_s
CONSTANT defaultInitValue
VARIABLES scan_tasks, response, scan_task_status, key_to_be_added_or_deleted, 
          pc, stack

(* define statement *)
TypeInvariant ==
  /\ response \in STRING
  /\ scan_task_status \in scan_task_statuses

VARIABLES key_, key_g, key_r, key_d, key_c, key_s, key

vars == << scan_tasks, response, scan_task_status, key_to_be_added_or_deleted, 
           pc, stack, key_, key_g, key_r, key_d, key_c, key_s, key >>

ProcSet == {"SCAN TASK"} \cup {"MAIN"}

Init == (* Global variables *)
        /\ scan_tasks = {}
        /\ response = ""
        /\ scan_task_status = "waiting"
        /\ key_to_be_added_or_deleted = ""
        (* Procedure add_config_keys *)
        /\ key_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_results *)
        /\ key_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure register_keys *)
        /\ key_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure delete_keys *)
        /\ key_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure clear_results *)
        /\ key_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure subscribe *)
        /\ key_s = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure scan *)
        /\ key = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "SCAN TASK" -> "AddTask"
                                        [] self = "MAIN" -> "ConfigGuard"]

AddConfigKeys(self) == /\ pc[self] = "AddConfigKeys"
                       /\ scan_task_status' = "adding"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ key_' = [key_ EXCEPT ![self] = Head(stack[self]).key_]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << scan_tasks, response, 
                                       key_to_be_added_or_deleted, key_g, 
                                       key_r, key_d, key_c, key_s, key >>

add_config_keys(self) == AddConfigKeys(self)

InfoService(self) == /\ pc[self] = "InfoService"
                     /\ response' = ToJson(info_response)
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << scan_tasks, scan_task_status, 
                                     key_to_be_added_or_deleted, key_, key_g, 
                                     key_r, key_d, key_c, key_s, key >>

get_info(self) == InfoService(self)

ResultsService(self) == /\ pc[self] = "ResultsService"
                        /\ IF key_g[self] \in scan_tasks
                              THEN /\ response' = ToJson(results_response)
                              ELSE /\ response' = ToJson("error")
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ key_g' = [key_g EXCEPT ![self] = Head(stack[self]).key_g]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << scan_tasks, scan_task_status, 
                                        key_to_be_added_or_deleted, key_, 
                                        key_r, key_d, key_c, key_s, key >>

get_results(self) == ResultsService(self)

RegisterService(self) == /\ pc[self] = "RegisterService"
                         /\ key_to_be_added_or_deleted' = key_r[self]
                         /\ scan_task_status' = "adding"
                         /\ response' = ToJson(register_response)
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ key_r' = [key_r EXCEPT ![self] = Head(stack[self]).key_r]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << scan_tasks, key_, key_g, key_d, key_c, 
                                         key_s, key >>

register_keys(self) == RegisterService(self)

DeleteService(self) == /\ pc[self] = "DeleteService"
                       /\ key_to_be_added_or_deleted' = key_d[self]
                       /\ scan_task_status' = "deleting"
                       /\ response' = ToJson(delete_response)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ key_d' = [key_d EXCEPT ![self] = Head(stack[self]).key_d]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << scan_tasks, key_, key_g, key_r, key_c, 
                                       key_s, key >>

delete_keys(self) == DeleteService(self)

ClearService(self) == /\ pc[self] = "ClearService"
                      /\ response' = ToJson(clear_response)
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ key_c' = [key_c EXCEPT ![self] = Head(stack[self]).key_c]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << scan_tasks, scan_task_status, 
                                      key_to_be_added_or_deleted, key_, key_g, 
                                      key_r, key_d, key_s, key >>

clear_results(self) == ClearService(self)

SubscribeService(self) == /\ pc[self] = "SubscribeService"
                          /\ response' = ToJson(subscribe_response)
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ key_s' = [key_s EXCEPT ![self] = Head(stack[self]).key_s]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << scan_tasks, scan_task_status, 
                                          key_to_be_added_or_deleted, key_, 
                                          key_g, key_r, key_d, key_c, key >>

subscribe(self) == SubscribeService(self)

ScanService(self) == /\ pc[self] = "ScanService"
                     /\ pc' = [pc EXCEPT ![self] = "ScanRegister"]
                     /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                     key_to_be_added_or_deleted, stack, key_, 
                                     key_g, key_r, key_d, key_c, key_s, key >>

ScanRegister(self) == /\ pc[self] = "ScanRegister"
                      /\ /\ key_r' = [key_r EXCEPT ![self] = key[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "register_keys",
                                                                  pc        |->  "ScanResults",
                                                                  key_r     |->  key_r[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "RegisterService"]
                      /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                      key_to_be_added_or_deleted, key_, key_g, 
                                      key_d, key_c, key_s, key >>

ScanResults(self) == /\ pc[self] = "ScanResults"
                     /\ /\ key_g' = [key_g EXCEPT ![self] = key[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_results",
                                                                 pc        |->  "ScanSubscribe",
                                                                 key_g     |->  key_g[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "ResultsService"]
                     /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                     key_to_be_added_or_deleted, key_, key_r, 
                                     key_d, key_c, key_s, key >>

ScanSubscribe(self) == /\ pc[self] = "ScanSubscribe"
                       /\ /\ key_s' = [key_s EXCEPT ![self] = key[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "subscribe",
                                                                   pc        |->  Head(stack[self]).pc,
                                                                   key_s     |->  key_s[self] ] >>
                                                               \o Tail(stack[self])]
                       /\ pc' = [pc EXCEPT ![self] = "SubscribeService"]
                       /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                       key_to_be_added_or_deleted, key_, key_g, 
                                       key_r, key_d, key_c, key >>

scan(self) == ScanService(self) \/ ScanRegister(self) \/ ScanResults(self)
                 \/ ScanSubscribe(self)

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
           /\ UNCHANGED << response, key_to_be_added_or_deleted, stack, key_, 
                           key_g, key_r, key_d, key_c, key_s, key >>

scantask == AddTask

ConfigGuard == /\ pc["MAIN"] = "ConfigGuard"
               /\ IF ConfigViewingKey # ""
                     THEN /\ pc' = [pc EXCEPT !["MAIN"] = "FromZebradConfig"]
                     ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningGuard"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_added_or_deleted, stack, key_, key_g, 
                               key_r, key_d, key_c, key_s, key >>

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
                                    key_to_be_added_or_deleted, key_g, key_r, 
                                    key_d, key_c, key_s, key >>

ListeningGuard == /\ pc["MAIN"] = "ListeningGuard"
                  /\ IF GrpcViewingKey # ""
                        THEN /\ pc' = [pc EXCEPT !["MAIN"] = "ListeningMode"]
                        ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_added_or_deleted, stack, key_, 
                                  key_g, key_r, key_d, key_c, key_s, key >>

ListeningMode == /\ pc["MAIN"] = "ListeningMode"
                 /\ \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetInfoCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "GetResultsCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterKeysCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteKeysCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ClearResultsCall"]
                    \/ /\ pc' = [pc EXCEPT !["MAIN"] = "ScanCall"]
                 /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                 key_to_be_added_or_deleted, stack, key_, 
                                 key_g, key_r, key_d, key_c, key_s, key >>

GetInfoCall == /\ pc["MAIN"] = "GetInfoCall"
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_info",
                                                          pc        |->  "End" ] >>
                                                      \o stack["MAIN"]]
               /\ pc' = [pc EXCEPT !["MAIN"] = "InfoService"]
               /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                               key_to_be_added_or_deleted, key_, key_g, key_r, 
                               key_d, key_c, key_s, key >>

GetResultsCall == /\ pc["MAIN"] = "GetResultsCall"
                  /\ /\ key_g' = [key_g EXCEPT !["MAIN"] = GrpcViewingKey]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "get_results",
                                                                pc        |->  "End",
                                                                key_g     |->  key_g["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "ResultsService"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_added_or_deleted, key_, key_r, 
                                  key_d, key_c, key_s, key >>

RegisterKeysCall == /\ pc["MAIN"] = "RegisterKeysCall"
                    /\ /\ key_r' = [key_r EXCEPT !["MAIN"] = GrpcViewingKey]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "register_keys",
                                                                  pc        |->  "End",
                                                                  key_r     |->  key_r["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "RegisterService"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_added_or_deleted, key_, key_g, 
                                    key_d, key_c, key_s, key >>

DeleteKeysCall == /\ pc["MAIN"] = "DeleteKeysCall"
                  /\ /\ key_d' = [key_d EXCEPT !["MAIN"] = GrpcViewingKey]
                     /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "delete_keys",
                                                                pc        |->  "End",
                                                                key_d     |->  key_d["MAIN"] ] >>
                                                            \o stack["MAIN"]]
                  /\ pc' = [pc EXCEPT !["MAIN"] = "DeleteService"]
                  /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                  key_to_be_added_or_deleted, key_, key_g, 
                                  key_r, key_c, key_s, key >>

ClearResultsCall == /\ pc["MAIN"] = "ClearResultsCall"
                    /\ /\ key_c' = [key_c EXCEPT !["MAIN"] = GrpcViewingKey]
                       /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "clear_results",
                                                                  pc        |->  "End",
                                                                  key_c     |->  key_c["MAIN"] ] >>
                                                              \o stack["MAIN"]]
                    /\ pc' = [pc EXCEPT !["MAIN"] = "ClearService"]
                    /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                                    key_to_be_added_or_deleted, key_, key_g, 
                                    key_r, key_d, key_s, key >>

ScanCall == /\ pc["MAIN"] = "ScanCall"
            /\ /\ key' = [key EXCEPT !["MAIN"] = GrpcViewingKey]
               /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "scan",
                                                          pc        |->  "End",
                                                          key       |->  key["MAIN"] ] >>
                                                      \o stack["MAIN"]]
            /\ pc' = [pc EXCEPT !["MAIN"] = "ScanService"]
            /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                            key_to_be_added_or_deleted, key_, key_g, key_r, 
                            key_d, key_c, key_s >>

End == /\ pc["MAIN"] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
       /\ UNCHANGED << scan_tasks, response, scan_task_status, 
                       key_to_be_added_or_deleted, stack, key_, key_g, key_r, 
                       key_d, key_c, key_s, key >>

MainLoop == ConfigGuard \/ FromZebradConfig \/ ListeningGuard
               \/ ListeningMode \/ GetInfoCall \/ GetResultsCall
               \/ RegisterKeysCall \/ DeleteKeysCall \/ ClearResultsCall
               \/ ScanCall \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == scantask \/ MainLoop
           \/ (\E self \in ProcSet:  \/ add_config_keys(self) \/ get_info(self)
                                     \/ get_results(self) \/ register_keys(self)
                                     \/ delete_keys(self) \/ clear_results(self)
                                     \/ subscribe(self) \/ scan(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Feb 29 20:39:40 UYT 2024 by alfredo
\* Created Wed Feb 21 10:40:53 UYT 2024 by alfredo
