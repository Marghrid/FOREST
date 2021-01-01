class Statistics:
    """ Singleton class to store synthesizer's statistics. """
    __instance__ = None

    def __init__(self):
        if Statistics.__instance__ is None:
            # timers:
            self.total_synthesis_time = 0.
            self.per_depth_times = {}

            self.regex_synthesis_time = 0.
            self.cap_groups_synthesis_time = 0.
            self.cap_conditions_synthesis_time = 0.

            self.first_regex_time = 0.

            self.regex_distinguishing_time = 0.
            self.cap_conditions_distinguishing_time = 0.

            # enumerated
            self.enumerated_regexes = 0
            self.enumerated_cap_groups = 0
            self.enumerated_cap_conditions = 0

            # interactions
            self.regex_interactions = 0
            self.cap_conditions_interactions = 0

            Statistics.__instance__ = self
        else:
            raise Exception("You cannot create another Statistics class")

    @staticmethod
    def get_statistics():
        """ Static method to fetch the current instance. """
        if not Statistics.__instance__:
            Statistics()
        return Statistics.__instance__

    def __str__(self):
        return \
            f'Elapsed time: {self.total_synthesis_time}\n' \
            f'Time per depth: {self.per_depth_times}\n\n' \
            f'Regex synthesis:\n' \
            f'  Regex time: {round(self.regex_synthesis_time, 2)}\n' \
            f'  First regex time: {round(self.first_regex_time, 2)}\n' \
            f'  Enumerated: {self.enumerated_regexes}\n' \
            f'  Interactions: {self.regex_interactions}\n' \
            f'  Distinguish time: {round(self.regex_distinguishing_time, 2)}\n' \
            f'Capturing groups synthesis:\n' \
            f'  Cap. groups time: {round(self.cap_groups_synthesis_time, 2)}\n' \
            f'  Enumerated: {self.enumerated_cap_groups}\n' \
            f'Capturing conditions synthesis:\n' \
            f'  Cap. conditions time: {round(self.cap_conditions_synthesis_time, 2)}\n' \
            f'  Enumerated: {self.enumerated_cap_conditions}\n' \
            f'  Interactions: {self.cap_conditions_interactions}\n' \
            f'  Distinguish time: {round(self.cap_conditions_distinguishing_time, 2)}'
