#!/usr/bin/env python3
#
# Copyright (c) 2019
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#    * Redistributions of source code must retain the above copyright
#      notice, this list of conditions and the following disclaimer.
#    * Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in the
#      documentation and/or other materials provided with the distribution.
#    * Neither the name of the CREATE-NET nor the
#      names of its contributors may be used to endorse or promote products
#      derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY CREATE-NET ''AS IS'' AND ANY
# EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL CREATE-NET BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""Simple wifi load balancing management app."""

from empower.core.app import EmpowerApp
from empower.core.resourcepool import BT_HT20
from empower.datatypes.etheraddress import EtherAddress
from empower.main import RUNTIME
from empower.lvapp.wifi_stats.wifi_stats import WiFiStats
from empower.apps.wifiloadbalancing import networkcoloring as nc
#TFM
from empower.lvapp.ucqm.ucqm import ucqm
from empower.lvapp.ucqm.ucqm import UCQMWorker
from empower.core.resourcepool import ResourceBlock
from empower.main import RUNTIME
from empower.core.lvap import PROCESS_SPAWNING
from empower.core.lvap import PROCESS_RUNNING
from empower.core.lvap import PROCESS_REMOVING

from functools import reduce
from collections import Counter
import time
import sys
import numpy as np#TFM
import random
import copy

RSSI_LIMIT = 10


class WifiLoadBalancing(EmpowerApp):
    """WifiLoadBalancing app.

    Command Line Parameters:

        period: loop period in ms (optional, default 5000ms)

    Example:

        ./empower-runtime.py apps.wifiloadbalancing.wifiloadbalancing \
            --tenant_id=52313ecb-9d00-4b7d-b873-b55d3d9ada00

    """

    def __init__(self, **kwargs):

        super().__init__(**kwargs)

        # app parameters
        self.ucqm_data = {}
        self.conflict_aps = {}
        self.aps_clients_matrix = {}
        self.clients_aps_matrix = {}

        self.handover_data = {}
        self.unsuccessful_handovers = {}
        self.aps_channel_utilization = {}
        self.scheduling_attempts = {}
        self.aps_counters = {}
        self.last_handover_time = 0
        #TFM
        self.channels = {}
        self.channels_bg = [1, 6, 10]
        #self.channels_an = []
        self.aps_clients_rel = {}
        self.common_initial_channel = random.choice(self.channels_bg)
        self.available_channels = {1,6,10}
        self.wtp_channel = {}
        self.wtp_average_rssi = {}
        self.channel_assignment = {}
        self.historic = {}
        self.receptors = {}
        self.wtp_rates = {}
        self.rates_n = \
            {
                0:6.5,
                1:13,
                2:19.5,
                3:26,
                4:39,
                5:52,
                6:58.5,
                7:65,
                8:13,
                9:26,
                10:39,
                11:52,
                12:78,
                13:104,
                14:117,
                15:130,
                16:19.5,
                17:39,
                18:58.5,
                19:78,
                20:117,
                21:156,
                22:175.5,
                23:195,
                24:26,
                25:52,
                26:78,
                27:104,
                28:156,
                29:208,
                30:234,
                31:260
            }

    def wtp_up(self, wtp):
        """Called when a new WTP connects to the controller."""
        
        for block in wtp.supports:

            self.ucqm(block=block,
                      every=self.every,
                      callback=self.ucqm_callback)
            self.wifi_stats(block=block,
                            every=self.every,
                            callback=self.wifi_stats_callback)

            if block.addr.to_str() not in self.conflict_aps:
                self.conflict_aps[block.addr] = []
            if block.channel not in self.channels: #add channel to list if not added yet
                self.channels[block.channel] = \
                    {
                        'load': 0,
                        'wtps':[],
                        'scheduling_attempts': 0,
                        'load_historic':[]
                    }
            if block.addr.to_str() not in self.aps_clients_matrix:
                self.aps_clients_matrix[block.addr] = []
            self.aps_channel_utilization[block.addr] = 0
            self.scheduling_attempts[block.addr] = \
                {
                    'rssi': 0,
                    'load': 0
                }
            self.historic[block.addr] = \
                {
                    'rssi': [],
                    'load': [],
                    'rssi_average': 0,
                    'load_average': 0
                }
            self.wtp_rates[block.addr] = \
                {
                    'best_probs':[],
                    'best_prob':0
                }
            self.aps_counters[block.addr] = {}
            self.channels[block.channel]['wtps'].append(block.addr) #stores each WTP channel

    def lvap_join(self, lvap):
        """Called when a new LVAP joins the network."""

        print("$$$$$$$ NUEVO LVAP $$$$$$$$", lvap.addr)
        self.bin_counter(lvap=lvap.addr,
                         every=self.every,
                         callback=self.counters_callback)

        self.receptors[lvap.addr] = \
            self.lvap_stats(lvap=lvap.addr, every=self.every)

        if lvap.wtp.addr.to_str() + lvap.addr.to_str() not in self.ucqm_data:
            self.ucqm_data[lvap.wtp.addr.to_str() + lvap.addr.to_str()] = \
                {
                    'rssi': None,
                    'wtp': lvap.blocks[0],
                    'lvap': lvap,
                    'active': 1,
                    'channel': lvap.blocks[0].channel,
                    'rssi_limit_counter' : 0
                }

        if lvap.addr not in self.aps_clients_matrix:
            self.aps_clients_matrix[lvap.wtp.addr].append(lvap)

        if lvap.addr not in self.clients_aps_matrix:
            self.clients_aps_matrix[lvap.addr] = []
            self.clients_aps_matrix[lvap.addr].append(lvap.blocks[0])

        if lvap.addr not in self.aps_counters[lvap.wtp.addr]:
            self.aps_counters[lvap.wtp.addr][lvap.addr] = \
                {
                    'tx_bytes_per_second': 0,
                    'rx_bytes_per_second': 0
                }

#    def lvap_leave(self, lvap):
#        self.aps_clients_matrix[lvap.wtp.addr].remove(lvap)

#    def wtp_down(self, wtp):
#        for block in wtp.supports:
#            self.channels[block.channel]['wtps'].remove(block.addr)


    def counters_callback(self, stats):
        """ New stats available. """

        lvap = RUNTIME.lvaps[stats.lvap]
        if not stats.tx_bytes_per_second or not stats.rx_bytes_per_second:
            return

        if lvap.wtp and lvap.addr:
            cnt = self.aps_counters[lvap.wtp.addr][lvap.addr]
        else:
            return

        cnt['tx_bytes_per_second'] = stats.tx_bytes_per_second[0]
        cnt['rx_bytes_per_second'] = stats.rx_bytes_per_second[0]

    def wifi_stats_callback(self, stats):
        """ New stats available. """
        # If there are no clients attached, it is not necessary to check the
        # channel utilization
        if not self.aps_clients_matrix[stats.block.addr]:
            self.aps_channel_utilization[stats.block.addr] = 0
            return

        if self.aps_counters[stats.block.addr].values():
            bytes_per_second = reduce(lambda x, y: dict((k, v + y[k]) for k, v in x.items()), self.aps_counters[stats.block.addr].values())
            if (stats.tx_per_second + stats.rx_per_second) == 0:
                if (bytes_per_second['tx_bytes_per_second'] + bytes_per_second['rx_bytes_per_second']) == 0:
                    self.aps_channel_utilization[stats.block.addr] = 0
                return
        else:
            self.aps_channel_utilization[stats.block.addr] = 0
            return
        # Rate probabilities: use to to balance with percentage instead of absolute load
        # best_probs = []
        # for lvap in self.aps_clients_matrix[stats.block.addr]:
        #      best_probs.append(self.receptors[lvap.addr].best_prob)

        # self.wtp_rates[stats.block.addr]['best_probs'] = best_probs
        # num,prob = max([(best_probs.count(prob),prob) for prob in set(best_probs)])
        # self.wtp_rates[stats.block.addr]['best_prob'] = prob
        # print("BEST  PROB OF WTP  ", stats.block.addr,  " IS ", prob)

        # Channel utilization
        previous_utilization = self.aps_channel_utilization[stats.block.addr]
        self.aps_channel_utilization[stats.block.addr] = (stats.tx_per_second + stats.rx_per_second)

        # historic
        self.historic[stats.block.addr]['load'].append((self.aps_channel_utilization[stats.block.addr]))# * self.rates_n[prob]) / 100)
        if len(self.historic[stats.block.addr]['load']) > 10:
            self.historic[stats.block.addr]['load'].pop(0)

        self.historic[stats.block.addr]['load_average'] = np.mean(self.historic[stats.block.addr]['load'])

        #usage_percentage = 0
        #for lvap in self.aps_counters[stats.block.addr]:
        #    print("ENTRO ", self.aps_counters[stats.block.addr][lvap]['rx_bytes_per_second'])
        #    usage_percentage += \
        #        (bytes_per_second['tx_bytes_per_second'] * 100 / self.rates_n[self.receptors[lvap].best_prob] + bytes_per_second['rx_bytes_per_second'] * 100 / self.rates_n[self.receptors[lvap].best_prob])

        #print("USAGE ", usage_percentage, " ", self.aps_channel_utilization[stats.block.addr])
        #Checks time from last handover or handover data
        if (time.time() - self.last_handover_time) < 5 or len(self.handover_data) != 0:
            return
        
        self.evaluate_thresholds(stats.block)       

    def channel_load_threshold(self):
        """ Computes channel load threshold """
        channel_load = {channel:0 for channel in self.channels}

        for channel in self.channels:
            self.channels[channel]['load'] = 0
            for wtp in self.aps_channel_utilization:
                if wtp in self.channels[channel]['wtps']: # if current channel is the used by this WTP, add utilization of WTP to channel total
                    self.channels[channel]['load'] += self.aps_channel_utilization[wtp] #Channel use per wtp
            self.channels[channel]['load_historic'].append(self.channels[channel]['load'])
            if len(self.channels[channel]['load_historic']) > 10 :
                self.channels[channel]['load_historic'].pop(0)
            channel_load[channel] = np.mean(self.channels[channel]['load_historic'])

        median = np.quantile(list(channel_load.values()),  0.5)
        maximum = np.amax(list(channel_load.values()))
        minimum = np.amin(list(channel_load.values()))
        print("CHANNEL LOAD THRESHOLD: ")
        print("\t Maximum ", maximum)
        print("\t Minimum ", minimum)
        print("\t Median ",  median)
        if (maximum - minimum) > median:
            for channel in self.channels:  
                if self.channels[channel]['load'] is maximum:
                    print("+++++++SUPERADO CHANNEL LOAD+++++ CANAL: ", self.channels[channel])
                    self.channels[channel]['scheduling_attempts'] += 1   
            return (True, channel)
        else:
            self.channels[channel]['scheduling_attempts'] = 0
            return (False, None)
    
    def wtp_load_threshold(self,wtp):
        """ Computes channel load threshold  with Q3 + 1,5 * IQR """
        wtp_loads = [dict['load_average'] for dict in self.historic.values()]
        median = np.quantile(wtp_loads, 0.5)
        maximum = np.amax(wtp_loads)
        minimum = np.amin(wtp_loads)
        print("WTP LOAD THRESHOLD: ")
        print("\t Maximum ", maximum)
        print("\t Minimum ", minimum)
        print("\t Median ",  median)
        if (maximum - minimum) > median:
            if self.historic[wtp]['load_average'] == maximum:
                print("+++++++SUPERADO EL WTP++++++++++ WTP: ", self.aps_channel_utilization)
                print("SCHEDULING ATTEPTS DE ",wtp," son ",self.scheduling_attempts[wtp])
                self.scheduling_attempts[wtp]['load'] += 1
            return True
        else:  
            if self.aps_channel_utilization[wtp] == maximum:
                self.scheduling_attempts[wtp]['load'] = 0
            return False 

    def RSSI_threshold(self,wtp):
        """Returns true if maximum RSSI - minimum RSSI is bigger than median RSSI"""
        self.average_RSSI_per_WTP()
        wtp_rssis = [dict['rssi_average'] for dict in self.historic.values()]
        maximum = np.amax(wtp_rssis)
        minimum = np.amin(wtp_rssis)
        median = np.quantile(wtp_rssis, 0.5)
        print("RSSI THRESHOLD: ")
        print("\t Maximum ", maximum)
        print("\t Minimum ", minimum)
        print("\t Median ",  median)
        if (maximum - minimum) > median:
            if self.historic[wtp]['rssi_average'] == maximum:
                print("+++++++SUPERADO EL RSSI++++++++++ WTP: ", self.historic[wtp]['rssi_average'])
                self.scheduling_attempts[wtp]['rssi'] += 1
                print("SCHEDULING ATTEPTS DE ",wtp," son ",self.scheduling_attempts[wtp])
            return True
        else:
            if self.historic[wtp]['rssi_average'] == maximum:
                self.scheduling_attempts[wtp]['rssi'] = 0
            return False 

    def evaluate_thresholds(self, block):
        """ Checks if any AP surpasses thresholds"""
        wtp_list = {wtp:RUNTIME.tenants[self.tenant.tenant_id].wtps[wtp] for wtp in RUNTIME.tenants[self.tenant.tenant_id].wtps if wtp in self.conflict_aps}
        lvap_list = {lvap:RUNTIME.tenants[self.tenant.tenant_id].lvaps[lvap] for lvap in RUNTIME.tenants[self.tenant.tenant_id].lvaps}
        #Debugging purposes
        for wtp in wtp_list:
            print("!!!!!!El WTP ", wtp, " tiene los clientes: ")
            for lvap in lvap_list:
                if lvap_list[lvap].wtp.addr is wtp :#and lvap_list[lvap].state is PROCESS_RUNNING:
                    print("! ", lvap)

        for channel in self.channels:
            print("___ El canal ", channel, "tiene ", self.channels[channel]['wtps'], " cargado con ", np.mean(self.channels[channel]['load_historic']))
        
        if self.handover_data:
            return

        wtp = block.addr
        print("self.scheduling_attempts",self.scheduling_attempts[wtp]['load'])
        if self.wtp_load_threshold(wtp) and self.scheduling_attempts[wtp]['load'] >= 4:
            # Reassign clients
            self.scheduling_attempts[wtp]['load'] = 0
            self.evaluate_handover(block)
            return

        elif self.RSSI_threshold(wtp) and not self.handover_data and self.scheduling_attempts[wtp]['rssi'] >= 4:
            print("Reorganizo por RSSI")
            # Reassign clients
            self.scheduling_attempts[wtp]['rssi'] = 0
            self.evaluate_handover(block)
            return

        if self.handover_data:
            return

        (thres, channel) = self.channel_load_threshold()
        if thres:
            if self.channels[channel]['scheduling_attempts'] >= 4:
                # Reassign channels
                self.channels[channel]['scheduling_attempts'] = 0
                self.network_coloring() 
                return

    def ucqm_callback(self, poller):
        """Called when a UCQM response is received from a WTP."""
        lvaps = RUNTIME.tenants[self.tenant.tenant_id].lvaps

        for lvap in poller.maps.values():
            key = poller.block.addr.to_str() + lvap['addr'].to_str() #key to access data concatenating block address and lvap address
            if lvap['addr'] in lvaps and lvaps[lvap['addr']].wtp:
                active_flag = 1
                if (lvaps[lvap['addr']].wtp.addr != poller.block.addr):
                    active_flag = 0
                elif ((lvaps[lvap['addr']].wtp.addr == poller.block.addr and (lvaps[lvap['addr']].association_state == False))):
                    active_flag = 0
                if key not in self.ucqm_data:
                    self.ucqm_data[key] = \
                    {
                        'rssi': lvap['mov_rssi'],
                        'wtp': poller.block,
                        'lvap': lvaps[lvap['addr']],
                        'active':active_flag,
                        'channel': poller.block.channel,
                        'rssi_limit_counter' : 0
                    }
                else:
                    self.ucqm_data[key]['rssi'] = lvap['mov_rssi']
                    self.ucqm_data[key]['active'] = active_flag
                # Conversion of the data structure to obtain the conflict APs
                if poller.block not in self.clients_aps_matrix[lvap['addr']]:
                    self.clients_aps_matrix[lvap['addr']].append(poller.block)
                if self.ucqm_data[key]['rssi'] < -80 and key in self.ucqm_data and not self.handover_data:
                    print("RSSI: ", self.ucqm_data[key]['rssi'], " WTP ", lvap, " intentos ", self.ucqm_data[key]['rssi_limit_counter'])
                    self.ucqm_data[key]['rssi_limit_counter'] += 1
                    if self.ucqm_data[key]['rssi_limit_counter'] >= 10:
                        self.evaluate_handover(lvaps[lvap['addr']].blocks[0])
                        self.ucqm_data[key]['rssi_limit_counter'] = 0
            elif key in self.ucqm_data:
                del self.ucqm_data[key]

            self.conflict_graph()

    def average_RSSI_per_WTP(self):
        """Computes average RSSI for all WTPs"""
        self.wtp_average_rssi = {wtp: 0 for wtp in self.aps_clients_matrix}

        for wtp in self.aps_clients_matrix:
            for lvap in self.aps_clients_matrix[wtp]:
                key = wtp.to_str() + lvap.addr.to_str()
                if key in self.ucqm_data and self.ucqm_data[key]['rssi']:
                    self.wtp_average_rssi[wtp] += self.ucqm_data[key]['rssi']

            if len(self.aps_clients_matrix[wtp]) is not 0:
                self.wtp_average_rssi[wtp] = abs(self.wtp_average_rssi[wtp] / len(self.aps_clients_matrix[wtp]))

            self.historic[wtp]['rssi'].append(self.wtp_average_rssi[wtp]) 
            if len(self.historic[wtp]['rssi']) > 10:
                self.historic[wtp]['rssi'].pop(0)
            self.historic[wtp]['rssi_average'] = np.mean(self.historic[wtp]['rssi'])

    def conflict_graph(self):
        """ Computes conflicting APs graph"""
        initial_conflict_graph = self.conflict_aps
        for wtp_list in self.clients_aps_matrix.values():
            for wtp in wtp_list:
                for conflict_wtp in wtp_list:
                    if conflict_wtp != wtp and (conflict_wtp not in self.conflict_aps[wtp.addr]):
                        self.conflict_aps[wtp.addr].append(conflict_wtp) #Íf a WTP is not itself and its not in the conflict graph it is added.

    def evaluate_handover(self, block):
        """Evaluates handover and does backtracking if handover breaks last iteration improvements"""
        ap_candidates = {}
        best_metric = sys.maxsize
        new_wtp = None
        new_lvap = None
        self.scheduling_attempts[block.addr]['rssi'] = 0
        self.scheduling_attempts[block.addr]['load'] = 0
        self.channels[block.channel]['scheduling_attempts'] = 0

        print("++++++++++++++++++EVALUATING HANDOVERS+++++++++++++++++++++++")
        for sta in self.aps_clients_matrix[block.addr]:
            for wtp in self.clients_aps_matrix[sta.addr]:
                key = wtp.addr.to_str() + sta.addr.to_str()
                if key in self.ucqm_data:
                    self.ucqm_data[key]['rssi_limit_counter'] = 0
                    if wtp == block or self.aps_channel_utilization[wtp.addr] > self.aps_channel_utilization[block.addr] or \
                        self.ucqm_data[key]['rssi'] < -75:
                        continue
                    if key in self.unsuccessful_handovers:
                        self.unsuccessful_handovers[key]['handover_retries'] += 1
                        if self.unsuccessful_handovers[key]['handover_retries'] < 5:
                            continue
                        del self.unsuccessful_handovers[key]

                conflict_occupancy = self.aps_channel_utilization[wtp.addr]
                for neighbour in self.conflict_aps[wtp.addr]:
                    if neighbour.channel == wtp.channel:
                        conflict_occupancy += self.aps_channel_utilization[neighbour.addr]
                wtp_info = \
                    {
                        'wtp': wtp,
                        #'metric' : abs(self.ucqm_data[key]['rssi']) * self.aps_channel_utilization[wtp.addr],
                        'metric': abs(self.ucqm_data[key]['rssi']) * (self.channels[wtp.channel]['load'] + self.aps_channel_utilization[wtp.addr]), #Evaluated metric for handover
                        'rssi': self.ucqm_data[key]['rssi']
                    }
                print("RSSI en wtp_info: ", wtp_info['rssi'], "del WTP", wtp_info['wtp'])
                ap_candidates[sta.addr] = []
                ap_candidates[sta.addr].append(wtp_info)

        ### Evaluation
        for sta, wtps in ap_candidates.items():
            for ap in wtps:
                if ((ap['metric'] < best_metric) or \
                    (ap['metric'] == best_metric and self.aps_channel_utilization[ap['wtp'].addr] < self.aps_channel_utilization[new_wtp.addr])) and (ap['rssi'] > -75) :
                    best_metric = ap['metric']
                    new_wtp = ap['wtp']
                    new_lvap = RUNTIME.lvaps[sta]
                    print("RSSI en wtp_info: ", ap['rssi'], "del WTP", ap['wtp'])

        if new_wtp is None or new_lvap is None:
            return

        print("####### HANDOVER DE ", block, " ", " HACIA ", new_wtp)
        if self.is_test_running() :
            self.handover_to_file(block, new_wtp, 'False')
        try:
            new_lvap.blocks = new_wtp
            old_ap = self.get_wtp_for_block(block)
            self.last_handover_time = time.time()
            self.handover_data[new_lvap.addr] = \
                {
                    'old_ap': old_ap,
                    'handover_ap': new_wtp,
                    'previous_channel_utilization': self.estimate_global_channel_utilization(),
                    'handover_time': time.time()
                }
            self.transfer_block_data(block, new_wtp, new_lvap)

        except ValueError:
            self.log.info("Handover already in progress for lvap %s" % new_lvap.addr.to_str())
            return

    def handover_to_file(self, src_wtp, dst_wtp, revert):
        """ Write handover to file """

        filename = "handovers.csv"

        line = "%s,%s,%s\n" % \
            (src_wtp, dst_wtp, revert)

        with open(filename, 'a') as file_d:
            file_d.write(line)

    def is_test_running(self):
        filename = "isTestActive"

        with open(filename, 'r') as file:
            for line in f:
                if line is 'True':
                    return True
                else:
                    return False

    def transfer_block_data(self, src_block, dst_block, lvap):
        print("////TRANSFERING ", lvap, " FROM ", src_block, " TO ", dst_block)
        self.scheduling_attempts[lvap.addr] = 0
        if lvap in self.aps_clients_matrix[src_block.addr]:
            self.aps_clients_matrix[src_block.addr].remove(lvap)
        if lvap not in self.aps_clients_matrix[dst_block.addr]:
            self.aps_clients_matrix[dst_block.addr].append(lvap)

        if lvap in self.aps_counters[src_block.addr][lvap.addr]:
            del self.aps_counters[src_block.addr][lvap.addr]
        self.aps_counters[dst_block.addr][lvap.addr] = \
            {
                'tx_bytes_per_second': 0,
                'rx_bytes_per_second': 0
            }

    def check_handover_performance(self):

        checked_clients = []
        for lvap, value in self.handover_data.items():
            if (time.time() - value['handover_time']) < 5:
                continue
            current_channel_utilization = self.estimate_global_channel_utilization()
            if value['previous_channel_utilization'] < current_channel_utilization and (current_channel_utilization - value['previous_channel_utilization']) > 20:
                self.revert_handover(lvap, current_channel_utilization)
            checked_clients.append(lvap)

        for entry in checked_clients:
            del self.handover_data[entry]

    def revert_handover(self, lvap_addr, current_channel_utilization):

        handover_ap = self.handover_data[lvap_addr]['handover_ap']
        old_ap = self.handover_data[lvap_addr]['old_ap']
        lvap = RUNTIME.lvaps[lvap_addr]
        print("Reverting handover")
        try:
            lvap.wtp = old_ap
            self.last_handover_time = time.time()
            key = handover_ap.addr.to_str() + lvap.addr.to_str()
            self.unsuccessful_handovers[key] = \
                {
                    'rssi': self.ucqm_data[key]['rssi'],
                    'previous_channel_utilization': current_channel_utilization,
                    'handover_retries': 0,
                    'old_ap': old_ap,
                    'handover_ap': handover_ap
                }
            self.transfer_block_data(handover_ap, old_ap, lvap)
            if self.is_test_running() :
                self.handover_to_file(handover_ap, old_ap, 'True')
        except ValueError:
            self.log.info("Handover already in progress for lvap %s" % lvap.addr.to_str())
            return

    def evalute_channel_utilization_difference(self, old_occupancy, new_occupancy, average_occupancy):

        if new_occupancy <= 10:
            return False
        if new_occupancy < (average_occupancy * 0.8) or new_occupancy > (average_occupancy * 1.2) or \
            new_occupancy < (old_occupancy * 0.8) or new_occupancy > (old_occupancy * 1.2):
            return True

        return False

    def delete_ucqm_worker(self, block):
        worker = RUNTIME.components[UCQMWorker.__module__]

        for module_id in list(worker.modules.keys()):
            ucqm_mod = worker.modules[module_id]
            if block == ucqm_mod.block:
                worker.remove_module(module_id)

    def update_block(self, block, channel):

        self.delete_ucqm_worker(block)

        block.channel = channel

        ucqm_mod = self.ucqm(block=block,
                        tenant_id=self.tenant.tenant_id,
                        every=self.every,
                        callback=self.ucqm_callback)

        if block.addr.to_str() in self.aps_clients_matrix:
            for lvap in self.aps_clients_matrix[block.addr.to_str()]:
                self.ucqm_data[block.addr.to_str() + lvap]['channel'] = channel


    def switch_channel_in_block(self, req_block, channel):

        if req_block.channel == channel:
            return

        wtps = RUNTIME.tenants[self.tenant.tenant_id].wtps
        lvaps = RUNTIME.tenants[self.tenant.tenant_id].lvaps

        for wtp in wtps.values():
            for block in wtp.supports:
                if block != req_block:
                    continue

                self.update_block(block, channel)

                for lvap in lvaps.values():
                    if lvap.blocks[0].addr != block.addr:
                        continue
                    lvap.scheduled_on = block

                if block.addr.to_str() not in self.aps_clients_matrix:
                    self.aps_clients_matrix[block.addr.to_str()] = []

                    for lvap in lvaps.values():
                        if lvap.blocks[0].addr != block.addr:
                            continue
                        self.aps_clients_matrix[block.addr.to_str()].append(lvap.addr.to_str())

                for lvap in self.aps_clients_matrix[block.addr.to_str()]:
                    self.ucqm_data[block.addr.to_str() + lvap]['channel'] = channel

                return

    def network_coloring(self):

        network_graph = {}
        conflict_aps = []
        for ap, conflict_list in self.conflict_aps.items():
            network_graph[ap.to_str()] = [conflict_ap.addr.to_str() for conflict_ap in conflict_list] # for each AP take APs in conflict (network_graph is a map of all the APs and its neighbours)

        network_graph = {n:neigh for n,neigh in network_graph.items() if neigh}

        coloring_channels = copy.deepcopy(self.available_channels)
        temp_channel_assignment = self.solve_channel_assignment(network_graph, coloring_channels, dict(), 0)
        if temp_channel_assignment and self.channel_assignment != temp_channel_assignment:
            self.channel_assignment = temp_channel_assignment

        print("*******************")
        print("Channel assignment: ", self.channel_assignment)
        print("*******************")

        for ap, channel in self.channel_assignment.items():
            block = self.get_block_for_ap_addr(ap)
            if block is None:
                continue
            self.switch_channel_in_block(block, channel)


    def find_best_candidate(self, graph, guesses):
        candidates_with_add_info = [
        (
        -len({guesses[neigh] for neigh in graph[n] if neigh     in guesses}), # channels that should not be assigned
        -len({neigh          for neigh in graph[n] if neigh not in guesses}), # nodes not colored yet
        n
        ) for n in graph if n not in guesses]

        candidates_with_add_info.sort()
        print("CANDIDATES ", candidates_with_add_info)
        candidates = [n for _,_,n in candidates_with_add_info]
        if candidates:
            candidate = candidates[0]
            return candidate
        return None


    def solve_channel_assignment(self, graph, channels, guesses, depth):
        n = self.find_best_candidate(graph, guesses)

        if n is None:
            return guesses # Solution is found

        for c in channels - {guesses[neigh] for neigh in graph[n] if neigh in guesses}:
            guesses[n] = c
            if self.estimate_channel_utilization(c, guesses) < self.threshold_channel_load :
                channels.remove(c)
            if self.solve_channel_assignment(graph, channels, guesses, depth+1):
                return guesses
            else:
                del guesses[n]
        return None

    def estimate_global_channel_utilization(self):

        utilization = 0
        for channel in self.channels:
            utilization += self.channels[channel]['load']

        return (utilization/len(self.channels))

    def estimate_channel_utilization(self, channel, guesses):

        utilization = 0
        wtps_in_channel = 0

        for wtp in guesses:
            if guesses[wtp] is channel:
                block = self.get_block_for_ap_addr(wtp)
                utilization += self.aps_channel_utilization[block.addr]
                wtps_in_channel += 1

        return utilization

    def get_block_for_ap_addr(self, addr):
        wtps = RUNTIME.tenants[self.tenant.tenant_id].wtps

        for wtp in wtps.values():
            for block in wtp.supports:
                if block.addr.to_str() != addr:
                    continue
                return block

        return None

    def get_wtp_for_block(self, block):
        wtps = RUNTIME.tenants[self.tenant.tenant_id].wtps

        for wtp in wtps:
            if str(block.addr) == str(wtp):
                return wtps[wtp]

        return None

    def loop(self):
        """ Periodic job. """

        if self.handover_data:
            self.check_handover_performance()

    def to_dict(self):
        """ Return a JSON-serializable."""

        out = super().to_dict()

        out['conflict_aps'] = \
            {str(k): (''.join(block.addr.to_str()) for block in v) for k, v in self.conflict_aps.items()}
        out['aps_clients_matrix'] = \
            {str(k): (''.join(lvap.addr.to_str()) for lvap in v) for k, v in self.aps_clients_matrix.items()}
        out['clients_aps_matrix'] = \
            {str(k): (''.join(block.addr.to_str()) for block in v) for k, v in self.clients_aps_matrix.items()}
        out['handover_data'] = \
            {str(k): {'old_ap':v['old_ap'].addr, 'handover_ap':v['handover_ap'].addr,  \
                        'previous_channel_utilization':v['previous_channel_utilization'], \
                        'handover_time':v['handover_time']} for k, v in self.handover_data.items()}
        out['unsuccessful_handovers'] = \
            {str(k): {'old_ap':v['old_ap'].addr, 'handover_ap':v['handover_ap'].addr, 'rssi':v['rssi'], \
                        'previous_channel_utilization':v['previous_channel_utilization'], 'handover_retries':v['handover_retries']} \
                        for k, v in self.unsuccessful_handovers.items()}
        out['aps_channel_utilization'] = \
            {str(k): v for k, v in self.aps_channel_utilization.items()}
        out['scheduling_attempts'] = \
            {str(k): v for k, v in self.scheduling_attempts.items()}
        out['ucqm_data'] = \
            {str(k): {'wtp':v['wtp'].addr, 'lvap':v['lvap'].addr, 'rssi':v['rssi'], \
                     'active':v['active']} for k, v in self.ucqm_data.items()}
        return out

def launch(tenant_id, every=1000):
    """ Initialize the module. """

    return WifiLoadBalancing(tenant_id=tenant_id, every=every)
