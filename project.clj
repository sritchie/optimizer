(defproject optimizer "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.5.1"]
                 [org.clojure/core.match "0.2.0-rc5"]]
  :profiles {:dev {:resource-paths ["dev"]
                   :dependencies [[midje "1.5.1"]]
                   :plugins [[lein-midje "3.0.0"]]}})
