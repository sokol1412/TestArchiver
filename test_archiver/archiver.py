# pylint: disable=C0103

import sys
import time
from collections import defaultdict
from datetime import datetime, timedelta
from hashlib import sha1

from . import archiver_listeners, database, version
from .configs import Config

config = Config()

SUPPORTED_TIMESTAMP_FORMATS = (
    "%Y%m%d %H:%M:%S.%f",
    "%Y-%m-%d %H:%M:%S.%fZ",
    "%Y-%m-%d %H:%M:%S.%f",
    "%Y-%m-%d %H:%M:%SZ",
    "%Y-%m-%d %H:%M:%S",
    "%Y%m%dT%H:%M:%S.%f",
    "%Y-%m-%dT%H:%M:%S.%f",
    "%Y-%m-%dT%H:%M:%S.%fZ",
    "%Y-%m-%dT%H:%M:%S.%f",
    "%Y-%m-%dT%H:%M:%SZ",
    "%Y-%m-%dT%H:%M:%S",
    "%Y-%m-%dT%H:%M:%S.%f%z",
)


class TimeAdjust:
    def __init__(self, secs, adjust_to_system):
        self._time_adjust_secs = secs
        self._adjust_to_system = adjust_to_system

    def secs(self):
        secs = self._time_adjust_secs
        if self._adjust_to_system:
            if time.daylight != 0 and time.localtime().tm_isdst:
                secs = secs + time.altzone
            else:
                secs = secs + time.timezone
        return secs


class TestItem:
    def __init__(self, archiver):
        self.archiver = archiver

    def parent_suite(self):
        for item in reversed(self.archiver.stack):
            if isinstance(item, Suite):
                return item
        return None

    def parent_test(self):
        for item in reversed(self.archiver.stack):
            if isinstance(item, Test):
                return item
        return None

    def _parent_item(self):
        return self.archiver.stack[-1] if self.archiver.stack else None

    def test_run_id(self):
        return self.archiver.test_run_id


class FingerprintedItem(TestItem):
    def __init__(self, archiver, name, class_name=None):
        super(FingerprintedItem, self).__init__(archiver)
        self.name = name
        self.parent_item = self._parent_item()
        if class_name:
            self.full_name = ".".join([class_name, name])
        elif not self.parent_item or not self.parent_item.full_name:
            self.full_name = self.name
        else:
            parent_prefix = self.parent_item.full_name + "." if self.parent_item else ""
            self.full_name = parent_prefix + self.name
        self.id = None

        self.status = None
        self.setup_status = None
        self.execution_status = None
        self.teardown_status = None
        self.failed_by_teardown = False

        self.start_time = None
        self.end_time = None
        self.elapsed_time = None
        self.elapsed_time_setup = None
        self.elapsed_time_execution = None
        self.elapsed_time_teardown = None
        self.critical = None

        self.kw_type = None
        self.kw_call_depth = 0
        self.library = None
        self.arguments = []
        self.tags = []
        self.metadata = {}
        self._last_metadata_name = None

        self.child_test_ids = []
        self.child_suite_ids = []

        self.subtree_fingerprints = []
        self.subtree_statuses = []
        self.fingerprint = None
        self.setup_fingerprint = None
        self.execution_fingerprint = None
        self.teardown_fingerprint = None

        self._execution_path = None
        self._child_counters = defaultdict(lambda: 0)

    def insert_results(self):
        raise NotImplementedError()

    def update_status(self, status, start_time, end_time, elapsed=None, critical=None):
        if status == "NOT_RUN":
            # If some keyword is not executed the execution was a dryrun
            self.archiver.output_from_dryrun = True
        self.status = status
        self.start_time = start_time
        self.end_time = end_time
        if self.start_time and self.end_time:
            start = adjusted_timestamp_to_datetime(
                self.start_time, self.archiver.time_adjust.secs()
            )
            end = adjusted_timestamp_to_datetime(
                self.end_time, self.archiver.time_adjust.secs()
            )
            self.elapsed_time = int((end - start).total_seconds() * 1000)
        elif elapsed is not None:
            self.elapsed_time = elapsed
        self.critical = critical

    def _hashing_name(self):
        return self.full_name

    def finish(self):
        self.execution_path()  # Make sure this is called before exiting any item
        self.handle_child_statuses()
        if not self.status:
            if self.execution_status:
                self.status = self.execution_status
            else:
                self.status = "PASS"
        if not self.elapsed_time:
            self.elapsed_time = (
                self.elapsed_time_setup
                if self.elapsed_time_setup
                else (
                    0 + self.elapsed_time_execution
                    if self.elapsed_time_execution
                    else (
                        0 + self.elapsed_time_teardown
                        if self.elapsed_time_teardown
                        else 0
                    )
                )
            )
        self.calculate_fingerprints()
        self.propagate_fingerprints_status_and_elapsed_time()
        self.insert_results()

    def calculate_fingerprints(self):
        """Calculate identification fingerprints using sha1 hashing."""
        # sha1 is not considered secure anymore but in this use case
        # it is not used for any security functionality.
        # sha1() lines marked nosec for Bandit linter to ignore.

        if self.subtree_fingerprints:
            execution = sha1()  # nosec
            for child in self.subtree_fingerprints:
                execution.update(child.encode("utf-8"))
            self.execution_fingerprint = execution.hexdigest()

        fingerprint = sha1()  # nosec
        fingerprint.update(self._hashing_name().encode("utf-8"))
        fingerprint.update(str(self.setup_fingerprint).encode("utf-8"))
        fingerprint.update(str(self.execution_fingerprint).encode("utf-8"))
        fingerprint.update(str(self.teardown_fingerprint).encode("utf-8"))
        fingerprint.update(str(self.status).encode("utf-8"))
        fingerprint.update(str(self.arguments).encode("utf-8"))
        fingerprint.update(str(self._execution_path).encode("utf-8"))
        self.fingerprint = fingerprint.hexdigest()

    def handle_child_statuses(self):
        if self.subtree_statuses:
            if "FAIL" in self.subtree_statuses:
                # Single child failure will fail the execution
                self.execution_status = "FAIL"
            elif "PASS" in self.subtree_statuses:
                # Single passing child execution and item is not considered to be skipped
                self.execution_status = "PASS"
            else:
                self.execution_status = "SKIPPED"

    def propagate_fingerprints_status_and_elapsed_time(self):
        if self.kw_type == "setup":
            self.parent_item.setup_fingerprint = self.fingerprint
            self.parent_item.setup_status = self.status
            self.parent_item.elapsed_time_setup = self.elapsed_time
        elif self.kw_type == "teardown":
            self.parent_item.teardown_fingerprint = self.fingerprint
            self.parent_item.teardown_status = self.status
            self.parent_item.elapsed_time_teardown = self.elapsed_time
        else:
            if self.parent_item:
                self.parent_item.subtree_fingerprints.append(self.fingerprint)
                self.parent_item.subtree_statuses.append(self.status)
                if self.elapsed_time:
                    if self.parent_item.elapsed_time_execution:
                        self.parent_item.elapsed_time_execution += self.elapsed_time
                    else:
                        self.parent_item.elapsed_time_execution = self.elapsed_time

    def status_and_fingerprint_values(self):
        return {
            "status": self.status,
            "setup_status": self.setup_status,
            "execution_status": self.execution_status,
            "teardown_status": self.teardown_status,
            "start_time": (
                adjusted_timestamp(self.start_time, self.archiver.time_adjust.secs())
                if self.start_time
                else None
            ),
            "elapsed": self.elapsed_time,
            "setup_elapsed": self.elapsed_time_setup,
            "execution_elapsed": self.elapsed_time_execution,
            "teardown_elapsed": self.elapsed_time_teardown,
            "fingerprint": self.fingerprint,
            "setup_fingerprint": self.setup_fingerprint,
            "execution_fingerprint": self.execution_fingerprint,
            "teardown_fingerprint": self.teardown_fingerprint,
        }

    def fail_children(self):
        for suite_id in self.child_suite_ids:
            key_values = {"suite_id": suite_id, "test_run_id": self.test_run_id()}
            self.archiver.db.update("suite_result", {"status": "FAIL"}, key_values)
        for test_id in self.child_test_ids:
            key_values = {"test_id": test_id, "test_run_id": self.test_run_id()}
            self.archiver.db.update("test_result", {"status": "FAIL"}, key_values)

    def set_execution_path(self, execution_path):
        self._execution_path = execution_path

    @staticmethod
    def _execution_path_identifier():
        return ""

    def child_counter(self, execution_path_identifier):
        self._child_counters[execution_path_identifier] += 1
        return self._child_counters[execution_path_identifier]

    def execution_path(self):
        if not self._execution_path:
            identifier = self._execution_path_identifier()
            if self.parent_item:
                identifier += str(
                    self.parent_item.child_counter(self._execution_path_identifier())
                )
            else:
                identifier += "1"
            if self.parent_item and self.parent_item.execution_path():
                self._execution_path = (
                    self.parent_item.execution_path() + "-" + identifier
                )
            else:
                self._execution_path = identifier
        return self._execution_path


class TestRun(FingerprintedItem):
    def __init__(self, archiver, archived_using, generated, generator, rpa, dryrun):
        super(TestRun, self).__init__(archiver, "")
        data = {
            "archived_using": archived_using,
            "archiver_version": version.ARCHIVER_VERSION,
            "generated": (
                adjusted_timestamp(generated, self.archiver.time_adjust.secs())
                if generated
                else None
            ),
            "generator": generator,
            "rpa": rpa,
            "dryrun": dryrun,
            "schema_version": self.archiver.db.current_schema_version(),
        }
        try:
            self.id = self.archiver.db.insert_and_return_id("test_run", data)
        except database.IntegrityError:
            raise database.IntegrityError(
                "ERROR: Unable to insert results. Probably the test archive schema is not "
                "compatible with the version of TestArchiver you are using. "
                "Consider updating to 2.0 or later."
            )

    def execution_path(self):
        return ""

    def insert_results(self):
        raise NotImplementedError()


class Suite(FingerprintedItem):
    def __init__(self, archiver, name, repository):
        super(Suite, self).__init__(archiver, name)
        data = {"full_name": self.full_name, "name": name, "repository": repository}
        self.id = self.archiver.db.return_id_or_insert_and_return_id(
            "suite", data, ["repository", "full_name"]
        )

    @staticmethod
    def _execution_path_identifier():
        return "s"

    def insert_results(self):
        data = {
            "suite_id": self.id,
            "test_run_id": self.test_run_id(),
            "execution_path": self.execution_path(),
        }
        self.status = "RUNNING"
        self.execution_status = "RUNNING"
        data.update(self.status_and_fingerprint_values())
        try:
            self.archiver.db.insert("suite_result", data)
        except database.IntegrityError:
            print(
                "[INSERT TO suite_result table] ERROR: database.IntegrityError: [INSERT] this suite_result have already been archived! Make sure the test suite names are unique within execution."
            )
            sys.exit(1)

    def finish(self):
        self.execution_path()  # Make sure this is called before exiting any item
        self.handle_child_statuses()
        if not self.status:
            if self.execution_status:
                self.status = self.execution_status
            else:
                self.status = "PASS"
        if not self.elapsed_time:
            self.elapsed_time = (
                self.elapsed_time_setup
                if self.elapsed_time_setup
                else (
                    0 + self.elapsed_time_execution
                    if self.elapsed_time_execution
                    else (
                        0 + self.elapsed_time_teardown
                        if self.elapsed_time_teardown
                        else 0
                    )
                )
            )
        self.calculate_fingerprints()
        self.propagate_fingerprints_status_and_elapsed_time()
        self.update_results()

    def update_results(self):
        data = self.status_and_fingerprint_values()
        if self.id not in self.parent_item.child_suite_ids:
            try:
                key_values = {"suite_id": self.id, "test_run_id": self.test_run_id()}
                self.archiver.db.update("suite_result", data, key_values)
            except database.IntegrityError:
                print(
                    "[UPDATE TO suite_result table] ERROR: database.IntegrityError: [UPDATE] this suite_result have already been archived! Make sure the test suite names are unique within execution."
                )
                sys.exit(1)
            self.insert_metadata()
            if self.failed_by_teardown:
                self.fail_children()
            if self.parent_item:
                self.parent_item.child_suite_ids.append(self.id)
                self.parent_item.child_suite_ids.extend(self.child_suite_ids)
                self.parent_item.child_test_ids.extend(self.child_test_ids)

        else:
            print(
                "WARNING: duplicate results for suite '{}' are ignored".format(
                    self.full_name
                )
            )

    def insert_metadata(self):
        # If the top suite add/override metadata with metadata given to archiver
        if isinstance(self.parent_item, TestRun):
            if self.archiver.additional_metadata:
                for name in self.archiver.additional_metadata:
                    self.metadata[name] = self.archiver.additional_metadata[name]
            if self.archiver.config.time_adjust_secs != 0:
                self.metadata["time_adjust_secs"] = (
                    self.archiver.config.time_adjust_secs
                )
            if self.archiver.config.time_adjust_with_system_timezone:
                self.metadata["time_adjust_secs_total"] = (
                    self.archiver.time_adjust.secs()
                )

        for name in self.metadata:
            content = self.metadata[name]
            data = {
                "name": name,
                "value": content,
                "suite_id": self.id,
                "test_run_id": self.test_run_id(),
            }
            self.archiver.db.insert("suite_metadata", data)
            if name.startswith("series"):
                if "#" in content:
                    series_name, build_number = content.split("#")
                else:
                    series_name, build_number = content, None
                self.archiver.test_series[series_name] = build_number
            elif name == "team":
                self.archiver.team = content

    def register_metadata(self, name=None, value=None):
        if name:
            self._last_metadata_name = name
        if value:
            self.metadata[self._last_metadata_name] = value


class SuiteXML(Suite):
    def __init__(self, archiver, name, repository):
        super(SuiteXML, self).__init__(archiver, name, repository)

    def finish(self):
        self.execution_path()  # Make sure this is called before exiting any item
        self.handle_child_statuses()
        if not self.status:
            if self.execution_status:
                self.status = self.execution_status
            else:
                self.status = "PASS"
        if not self.elapsed_time:
            self.elapsed_time = (
                self.elapsed_time_setup
                if self.elapsed_time_setup
                else (
                    0 + self.elapsed_time_execution
                    if self.elapsed_time_execution
                    else (
                        0 + self.elapsed_time_teardown
                        if self.elapsed_time_teardown
                        else 0
                    )
                )
            )
        self.calculate_fingerprints()
        self.propagate_fingerprints_status_and_elapsed_time()
        self.insert_results()

    def insert_results(self):
        data = {
            "suite_id": self.id,
            "test_run_id": self.test_run_id(),
            "execution_path": self.execution_path(),
        }
        data.update(self.status_and_fingerprint_values())
        if self.id not in self.parent_item.child_suite_ids:
            try:
                self.archiver.db.insert("suite_result", data)
            except database.IntegrityError:
                print(
                    "[INSERT TO suite_result table] ERROR: database.IntegrityError: [INSERT] this suite_result have already been archived! Make sure the test suite names are unique within execution."
                )
                sys.exit(1)
            self.insert_metadata()
            if self.failed_by_teardown:
                self.fail_children()
            if self.parent_item:
                self.parent_item.child_suite_ids.append(self.id)
                self.parent_item.child_suite_ids.extend(self.child_suite_ids)
                self.parent_item.child_test_ids.extend(self.child_test_ids)

        else:
            print(
                "WARNING: duplicate results for suite '{}' are ignored".format(
                    self.full_name
                )
            )


class Test(FingerprintedItem):
    def __init__(self, archiver, name, class_name):
        super(Test, self).__init__(archiver, name, class_name)
        self.execution_keyword_order = 1
        data = {
            "full_name": self.full_name,
            "name": name,
            "suite_id": self.parent_item.id,
        }
        self.id = self.archiver.db.return_id_or_insert_and_return_id(
            "test_case", data, ["suite_id", "full_name"]
        )

    @staticmethod
    def _execution_path_identifier():
        return "t"

    def finish(self):
        self.execution_path()  # Make sure this is called before exiting any item
        self.handle_child_statuses()
        if not self.status:
            if self.execution_status:
                self.status = self.execution_status
            else:
                self.status = "PASS"
        if not self.elapsed_time:
            self.elapsed_time = (
                self.elapsed_time_setup
                if self.elapsed_time_setup
                else (
                    0 + self.elapsed_time_execution
                    if self.elapsed_time_execution
                    else (
                        0 + self.elapsed_time_teardown
                        if self.elapsed_time_teardown
                        else 0
                    )
                )
            )
        self.calculate_fingerprints()
        self.propagate_fingerprints_status_and_elapsed_time()
        self.update_results()
        # Remove running keywords data from DB as test is finished and we don't need it anymore so we can save some space in database
        self.remove_running_parent_keywords_data()

    def remove_running_parent_keywords_data(self):
        if self.archiver.config.archive_keywords:
            test_run_id = self.test_run_id()
            suite_id = self.parent_item.id
            test_id = self.id
            key_values = {
                "test_run_id": test_run_id,
                "suite_id": suite_id,
                "test_id": test_id,
            }
            self.archiver.db.delete("running_parent_keywords", key_values)

    def insert_results(self):
        data = {
            "test_id": self.id,
            "test_run_id": self.test_run_id(),
            "critical": self.critical,
            "status": self.status,
            "execution_path": self.execution_path(),
        }
        try:
            self.archiver.db.insert("test_result", data)
        except database.IntegrityError:
            print(
                "[INSERT TO test_result table] ERROR: database.IntegrityError: [INSERT] this test_result have already been archived! Make sure the test case names are unique within each test suite!"
            )
            sys.exit(1)

    def update_running_status(self):
        data = self.status_and_fingerprint_values()
        key_values = {"test_id": self.id, "test_run_id": self.test_run_id()}
        self.archiver.db.update("test_result", data, key_values)

    def update_results(self):
        if self.id not in self.parent_item.child_test_ids:
            data = {
                "test_id": self.id,
                "test_run_id": self.test_run_id(),
                "critical": self.critical,
                "execution_path": self.execution_path(),
            }
            data.update(self.status_and_fingerprint_values())
            key_values = {"test_id": self.id, "test_run_id": self.test_run_id()}
            self.archiver.db.update("test_result", data, key_values)
            if self.subtree_fingerprints and self.archiver.config.archive_keywords:
                data = {
                    "fingerprint": self.execution_fingerprint,
                    "keyword": None,
                    "library": None,
                    "status": self.execution_status,
                    "arguments": self.arguments,
                }
                self.archiver.db.insert_or_ignore("keyword_tree", data, ["fingerprint"])
            if self.archiver.config.archive_keywords:
                self.insert_subtrees()
            self.insert_tags()
            self.parent_item.child_test_ids.append(self.id)
        else:
            print(
                "WARNING: duplicate results for test '{}' are ignored".format(
                    self.full_name
                )
            )

    def insert_tags(self):
        for tag in self.tags:
            data = {"tag": tag, "test_id": self.id, "test_run_id": self.test_run_id()}
            self.archiver.db.insert("test_tag", data)

    def insert_subtrees(self):
        call_index = 1
        for subtree in self.subtree_fingerprints:
            data = {
                "fingerprint": self.execution_fingerprint,
                "subtree": subtree,
                "call_index": call_index,
            }
            key_values = ["fingerprint", "subtree", "call_index"]
            self.archiver.db.insert_or_ignore("tree_hierarchy", data, key_values)
            call_index += 1


class TestXML(Test):
    def __init__(self, archiver, name, class_name):
        super(TestXML, self).__init__(archiver, name, class_name)

    def finish(self):
        self.execution_path()  # Make sure this is called before exiting any item
        self.handle_child_statuses()
        if not self.status:
            if self.execution_status:
                self.status = self.execution_status
            else:
                self.status = "PASS"
        if not self.elapsed_time:
            self.elapsed_time = (
                self.elapsed_time_setup
                if self.elapsed_time_setup
                else (
                    0 + self.elapsed_time_execution
                    if self.elapsed_time_execution
                    else (
                        0 + self.elapsed_time_teardown
                        if self.elapsed_time_teardown
                        else 0
                    )
                )
            )
        self.calculate_fingerprints()
        self.propagate_fingerprints_status_and_elapsed_time()
        self.insert_results()

    def insert_results(self):
        if self.id not in self.parent_item.child_test_ids:
            data = {
                "test_id": self.id,
                "test_run_id": self.test_run_id(),
                "critical": self.critical,
                "execution_path": self.execution_path(),
            }
            data.update(self.status_and_fingerprint_values())
            self.archiver.db.insert("test_result", data)
            if self.subtree_fingerprints and self.archiver.config.archive_keywords:
                data = {
                    "fingerprint": self.execution_fingerprint,
                    "keyword": None,
                    "library": None,
                    "status": self.execution_status,
                    "arguments": self.arguments,
                }
                self.archiver.db.insert_or_ignore("keyword_tree", data, ["fingerprint"])
            if self.archiver.config.archive_keywords:
                self.insert_subtrees()
            self.insert_tags()
            self.parent_item.child_test_ids.append(self.id)
        else:
            print(
                "WARNING: duplicate results for test '{}' are ignored".format(
                    self.full_name
                )
            )


class Keyword(FingerprintedItem):
    def __init__(self, archiver, name, library, kw_type, arguments):
        super(Keyword, self).__init__(archiver, name)
        self.library = library
        self.kw_type = kw_type
        self.kw_call_depth = self.parent_item.kw_call_depth + 1
        if arguments:
            self.arguments.extend(arguments)

    @staticmethod
    def _execution_path_identifier():
        return "k"

    def insert_running_parent_keyword_results(self):
        if self.archiver.config.archive_keywords:
            suite_id = self.parent_item.parent_item.id
            test_id = self.parent_item.id
            if self.kw_type == "keyword":
                self.kw_type = "EXECUTION"
                keyword_order = self.parent_item.execution_keyword_order
                self.parent_item.execution_keyword_order += 1
            elif self.kw_type == "setup":
                keyword_order = 0
            elif self.kw_type == "teardown":
                keyword_order = 999999

            data = {
                "test_run_id": self.archiver.test_run_id,
                "suite_id": suite_id,
                "test_id": test_id,
                "execution_path": self.execution_path(),
                "keyword": self.name,
                "keyword_type": self.kw_type.upper(),
                "keyword_order": keyword_order,
                "status": "RUNNING",
                "library": self.library,
                "arguments": self.arguments,
            }
            self.archiver.db.insert_or_ignore(
                "running_parent_keywords",
                data,
                ["test_run_id", "suite_id", "test_id", "execution_path"],
            )

    def update_finished_parent_keyword_results(self):
        if self.archiver.config.archive_keywords:
            suite_id = self.parent_item.parent_item.id
            test_id = self.parent_item.id
            data = {"status": self.status, "keyword_elapsed": self.elapsed_time}
            key_values = {
                "test_run_id": self.archiver.test_run_id,
                "suite_id": suite_id,
                "test_id": test_id,
                "execution_path": self._execution_path,
            }
            self.archiver.db.update("running_parent_keywords", data, key_values)

    def insert_results(self):
        if self.kw_type == "teardown" and self.status == "FAIL":
            self.parent_item.failed_by_teardown = True
        if self.archiver.config.archive_keywords:
            data = {
                "fingerprint": self.fingerprint,
                "keyword": self.name,
                "library": self.library,
                "status": self.status,
                "arguments": self.arguments,
                "execution_path": self.execution_path(),
            }
            self.archiver.db.insert_or_ignore("keyword_tree", data, ["fingerprint"])
            self.insert_subtrees()
            if self.archiver.config.archive_keyword_statistics:
                self.update_statistics()

    def insert_subtrees(self):
        call_index = 1
        for subtree in self.subtree_fingerprints:
            data = {
                "fingerprint": self.fingerprint,
                "subtree": subtree,
                "call_index": call_index,
            }
            key_values = ["fingerprint", "subtree", "call_index"]
            self.archiver.db.insert_or_ignore("tree_hierarchy", data, key_values)
            call_index += 1

    def _hashing_name(self):
        return self.library + "." + self.name

    def update_statistics(self):
        if self.fingerprint in self.archiver.keyword_statistics:
            stat_object = self.archiver.keyword_statistics[self.fingerprint]
            stat_object["calls"] += 1
            if self.elapsed_time:
                if stat_object["max_execution_time"] is None:
                    stat_object["max_execution_time"] = self.elapsed_time
                else:
                    stat_object["max_execution_time"] = max(
                        stat_object["max_execution_time"], self.elapsed_time
                    )
                if stat_object["min_execution_time"] is None:
                    stat_object["min_execution_time"] = self.elapsed_time
                else:
                    stat_object["min_execution_time"] = min(
                        stat_object["min_execution_time"], self.elapsed_time
                    )
                if stat_object["cumulative_execution_time"] is None:
                    stat_object["cumulative_execution_time"] = self.elapsed_time
                else:
                    stat_object["cumulative_execution_time"] += self.elapsed_time
            stat_object["max_call_depth"] = max(
                stat_object["max_call_depth"], self.kw_call_depth
            )
        else:
            self.archiver.keyword_statistics[self.fingerprint] = {
                "fingerprint": self.fingerprint,
                "test_run_id": self.test_run_id(),
                "calls": 1,
                "max_execution_time": self.elapsed_time,
                "min_execution_time": self.elapsed_time,
                "cumulative_execution_time": self.elapsed_time,
                "max_call_depth": self.kw_call_depth,
            }
        if (
            self.archiver.config.archive_keywords
            and self.archiver.config.archive_keyword_statistics
        ):
            self.archiver.db.insert(
                "keyword_statistics", self.archiver.keyword_statistics[self.fingerprint]
            )


class LogMessage(TestItem):
    def __init__(self, archiver, log_level, timestamp, message):
        super(LogMessage, self).__init__(archiver)
        self.parent_item = self._parent_item()
        self.log_level = log_level
        self.timestamp = timestamp
        self.raw_message = message
        self.id = None
        self._time_adjust = TimeAdjust(
            archiver.config.time_adjust_secs,
            archiver.config.time_adjust_with_system_timezone,
        )

    def insert(self):
        if (
            not self.archiver.config.ignore_logs
            and not self.archiver.config.log_level_ignored(self.log_level)
        ):
            message_length = config.max_log_message_length

            if message_length < 0:
                message = self.raw_message[message_length:]
            elif message_length > 0:
                message = self.raw_message[:message_length]
            else:
                message = self.raw_message
            data = {
                "test_run_id": self.test_run_id(),
                "timestamp": adjusted_timestamp(
                    self.timestamp, self.archiver.time_adjust.secs()
                ),
                "log_level": self.log_level,
                "message": message,
                "test_id": self.parent_test().id if self.parent_test() else None,
                "suite_id": self.parent_suite().id,
                "execution_path": self.execution_path(),
            }
            self.id = self.archiver.db.insert("log_message", data)

    def prepare_insert_value_row(self):
        if (
            not self.archiver.config.ignore_logs
            and not self.archiver.config.log_level_ignored(self.log_level)
        ):
            message_length = config.max_log_message_length

            if message_length < 0:
                message = self.raw_message[message_length:]
            elif message_length > 0:
                message = self.raw_message[:message_length]
            else:
                message = self.raw_message
            data = (
                self.test_run_id(),
                adjusted_timestamp(self.timestamp, self.archiver.time_adjust.secs()),
                self.log_level,
                message,
                self.parent_test().id if self.parent_test() else None,
                self.parent_suite().id,
                self.execution_path(),
            )
            return data

    @staticmethod
    def get_columns():
        return (
            "test_run_id",
            "timestamp",
            "log_level",
            "message",
            "test_id",
            "suite_id",
            "execution_path",
        )

    def execution_path(self):
        return self.parent_item.execution_path()


def database_connection(configuration):
    return database.get_connection_and_check_schema(configuration)


class Archiver:
    def __init__(self, connection, configuration, build_number_cache=None):
        self.count = 0
        self.config = configuration
        self.test_type = None
        self.additional_metadata = self.config.metadata
        self.test_run_id = None
        self.test_series = {}
        self.team = self.config.team
        self.series = self.config.series
        self.repository = self.config.repository

        self.archived_using = None
        self.output_from_dryrun = False
        self.db = connection
        self.stack = []
        self.logs_stack = []
        self.keyword_statistics = {}
        self.build_number_cache = build_number_cache or {}
        self.execution_context = self.config.execution_context
        self.changes = self.config.changes
        self.execution_id = self.config.execution_id

        self.time_adjust = TimeAdjust(
            self.config.time_adjust_secs, self.config.time_adjust_with_system_timezone
        )

        self.listeners = []
        if self.config.change_engine_url:
            self.listeners.append(
                archiver_listeners.ChangeEngineListener(
                    self, self.config.change_engine_url
                )
            )

    def current_item(self, expected_type=None):
        item = self.stack[-1] if self.stack else None
        if expected_type:
            if not isinstance(item, expected_type):
                raise Exception(
                    "Expected to have '{}' but had '{}' currently in stack".format(
                        expected_type, item.__class__.__name__
                    )
                )
        return item

    def current_item_is_keyword(self):
        if isinstance(self.current_item(), Keyword):
            return True
        return False

    def current_item_is_test(self):
        if isinstance(self.current_item(), Test):
            return True
        return False

    def current_item_is_suite(self):
        if isinstance(self.current_item(), Suite):
            return True
        return False

    def current_suite(self):
        if self.current_item():
            return self.current_item().parent_suite()
        return None

    def current_suites(self):
        return [item for item in self.stack if isinstance(item, Suite)]

    def current_keyword(self):
        keyword = self.current_item(Keyword)
        return keyword

    def begin_test_run(self, archived_using, generated, generator, rpa, dryrun):
        test_run = TestRun(self, archived_using, generated, generator, rpa, dryrun)
        self.archived_using = archived_using
        self.test_run_id = test_run.id
        self.stack.append(test_run)

    def update_dryrun_status(self):
        data = {"dryrun": self.output_from_dryrun}
        self.db.update("test_run", data, {"id": self.test_run_id})

    def end_test_run(self):
        for content in self.config.series:
            if "#" in content:
                series_name, build_number = content.split("#")
            else:
                series_name, build_number = content, None
            self.test_series[series_name] = build_number
        for name in self.test_series:
            self.report_series(name, self.test_series[name])
        if not self.test_series:
            self.report_series("default series", None)
        self.report_series("All builds", None)

        self.db.commit()
        for listener in self.listeners:
            listener.end_run()

        return self.build_number_cache

    def report_series(self, name, build_id):
        data = {"team": self.team if self.team else "No team", "name": name}
        series_id = self.db.return_id_or_insert_and_return_id(
            "test_series", data, ["team", "name"]
        )
        if build_id:
            try:
                build_number = int(build_id)
            except ValueError:
                build_number = self._build_number_by_id(series_id, build_id)
        else:
            if series_id in self.build_number_cache:
                build_number = self.build_number_cache[series_id]
            else:
                previous_build_number = self.db.max_value(
                    "test_series_mapping", "build_number", {"series": series_id}
                )
                build_number = previous_build_number + 1 if previous_build_number else 1
                self.build_number_cache[series_id] = build_number
        data = {
            "series": series_id,
            "test_run_id": self.test_run_id,
            "build_number": build_number,
            "build_id": build_id,
        }
        self.db.insert("test_series_mapping", data)

    def _build_number_by_id(self, series_id, build_id):
        build_number = self.db.fetch_one_value(
            "test_series_mapping",
            "build_number",
            {"build_id": build_id, "series": series_id},
        )
        if not build_number:
            previous_build_number = self.db.max_value(
                "test_series_mapping", "build_number", {"series": series_id}
            )
            build_number = previous_build_number + 1 if previous_build_number else 1
        return build_number

    def begin_suite(self, name, tests=None, execution_path=None):
        suite = Suite(self, name, "repo")
        suite.set_execution_path(execution_path)
        self.stack.append(suite)
        if tests:
            sut: Suite = self.begin_suite(name)
            sut.insert_results()
            for test in tests:
                tc: Test = self.create_test(test)
                tc.status = "NOT_RUN"
                tc.execution_status = "NOT_RUN"
                tc.insert_results()
        return suite

    def begin_suite_xml(self, name, execution_path=None):
        suite = SuiteXML(self, name, "repo")
        suite.set_execution_path(execution_path)
        self.stack.append(suite)
        return suite

    def end_suite(self, attributes=None):
        if attributes:
            self.current_item(Suite).update_status(
                attributes["status"], attributes["starttime"], attributes["endtime"]
            )
            self.current_item(Suite).metadata = attributes["metadata"]
        self.current_item(Suite).finish()
        suite = self.stack.pop()
        for listener in self.listeners:
            listener.suite_result(suite)

    def end_suite_xml(self, attributes=None):
        if attributes:
            self.current_item(SuiteXML).update_status(
                attributes["status"], attributes["starttime"], attributes["endtime"]
            )
            self.current_item(SuiteXML).metadata = attributes["metadata"]
        self.current_item(SuiteXML).finish()
        suite = self.stack.pop()
        for listener in self.listeners:
            listener.suite_result(suite)

    def begin_test(self, name, class_name=None, execution_path=None):
        test = Test(self, name, class_name)
        test.set_execution_path(execution_path)
        self.stack.append(test)
        test.status = "RUNNING"
        test.update_running_status()
        return test

    def create_test(self, name, class_name=None, execution_path=None):
        test = Test(self, name, class_name)
        return test

    def begin_test_xml(self, name, class_name=None, execution_path=None):
        test = TestXML(self, name, class_name)
        test.set_execution_path(execution_path)
        self.stack.append(test)
        return test

    def end_test(self, attributes=None):
        if attributes:
            critical = (
                attributes["critical"] == "yes" if "critical" in attributes else None
            )
            self.current_item(Test).update_status(
                attributes["status"],
                attributes["starttime"],
                attributes["endtime"],
                critical=critical,
            )
            self.current_item(Test).tags = attributes["tags"]
        self.current_item(Test).finish()
        test = self.stack.pop()
        for listener in self.listeners:
            listener.test_result(test)

    def end_test_xml(self, attributes=None):
        if attributes:
            critical = (
                attributes["critical"] == "yes" if "critical" in attributes else None
            )
            self.current_item(TestXML).update_status(
                attributes["status"],
                attributes["starttime"],
                attributes["endtime"],
                critical=critical,
            )
            self.current_item(TestXML).tags = attributes["tags"]
        self.current_item(TestXML).finish()
        test = self.stack.pop()
        for listener in self.listeners:
            listener.test_result(test)

    def begin_status(
        self, status, start_time=None, end_time=None, elapsed=None, critical=None
    ):
        self.current_item().update_status(
            status, start_time, end_time, elapsed, critical
        )

    def update_status(self, status):
        self.current_item().status = status

    def begin_keyword(
        self, name, library, kw_type, arguments=None, execution_path=None
    ):
        keyword = Keyword(self, name, library, kw_type.lower(), arguments)
        keyword.set_execution_path(execution_path)
        if type(keyword.parent_item) == Test:
            keyword.insert_running_parent_keyword_results()
        self.stack.append(keyword)
        return keyword

    def end_keyword(self, attributes=None):
        keyword: Keyword = self.current_item(Keyword)
        if keyword.kw_call_depth == 1:
            self.count += 1
            self.db.bulk_insert(
                "log_message", self.logs_stack, LogMessage.get_columns()
            )
            self.logs_stack = []
        if attributes:
            keyword.update_status(
                attributes["status"], attributes["starttime"], attributes["endtime"]
            )
        if type(keyword.parent_item) == Test:
            keyword.update_finished_parent_keyword_results()
        self.current_item(Keyword).finish()
        self.stack.pop()

    def keyword(self, name, library, kw_type, status, arguments=None):
        keyword = self.begin_keyword(name, library, kw_type, arguments)
        self.update_status(status)
        self.end_keyword()
        return keyword

    def update_arguments(self, argument):
        self.current_item(Keyword).arguments.append(argument)

    def update_tags(self, tag):
        self.current_item(Test).tags.append(tag)

    def metadata(self, name, content):
        self.begin_metadata(name)
        self.end_metadata(content)

    def begin_metadata(self, name):
        self.current_item(Suite).register_metadata(name=name)

    def end_metadata(self, content):
        self.current_item(Suite).register_metadata(value=content)

    def log_message(self, level, content, timestamp=None):
        self.begin_log_message(level, timestamp)

    def begin_log_message(self, level, message, timestamp=None):
        self.stack.append(LogMessage(self, level, timestamp, message=message))

    def finalize_log_messages(self):
        is_log_message = True
        while is_log_message:
            item = None
            if self.stack:
                item = self.stack[-1]
            else:
                return
            if isinstance(item, LogMessage):
                item: LogMessage
                self.logs_stack.append(item.prepare_insert_value_row())
                self.stack.pop()
            else:
                is_log_message = False

    def report_keyword_statistics(self):
        for fingerprint in self.keyword_statistics:
            self.db.insert("keyword_statistics", self.keyword_statistics[fingerprint])


def timestamp_to_datetime(timestamp):
    for timestamp_format in SUPPORTED_TIMESTAMP_FORMATS:
        try:
            parsed_datetime = datetime.strptime(timestamp, timestamp_format)
            return parsed_datetime
        except ValueError:
            pass
    raise Exception("timestamp: '{}' is in unsupported format".format(timestamp))


def adjusted_timestamp_to_datetime(timestamp, time_adjust_secs=0):
    adjusted_datetime = timestamp_to_datetime(timestamp)
    adjustment = abs(time_adjust_secs)
    if time_adjust_secs > 0:
        adjusted_datetime = adjusted_datetime + timedelta(seconds=adjustment)
    elif time_adjust_secs < 0:
        adjusted_datetime = adjusted_datetime - timedelta(seconds=adjustment)
    return adjusted_datetime


def adjusted_timestamp(timestamp, time_adjust_secs=0):
    adjusted_stamp = timestamp
    if timestamp and time_adjust_secs != 0:
        adjusted_datetime = adjusted_timestamp_to_datetime(timestamp, time_adjust_secs)
        adjusted_stamp = adjusted_datetime.isoformat(timespec="milliseconds")
    return adjusted_stamp
