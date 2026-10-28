module Ogre = struct
  external normalize : string -> (string, string) result = "ogre_rs_parse"
  external merge : string -> string -> (string, string) result = "ogre_rs_merge"
  external yaml : string -> (string, string) result = "ogre_rs_yaml"
  external json : string -> (string, string) result = "ogre_rs_json"
end
