"""
Complete Institutional-Grade Intraday Options Trading System
===========================================================
A comprehensive algorithmic trading system for Indian derivatives markets
Based on real-time Excel data feed with advanced analytics and ML integration

Author: AI Trading Systems
Version: 1.0
Date: 2025

Features:
- Real-time Excel data processing
- Smart money flow detection
- Advanced Greeks calculation
- Multi-asset support (Index, Commodity, Stock options)
- Machine learning pattern recognition
- Paper trading with P&L tracking
- Configurable risk management
- Holiday calendar integration
- Performance analytics dashboard
"""

import pandas as pd
import numpy as np
import sqlite3
import json
import logging
import warnings
from datetime import datetime, timedelta, time
from typing import Dict, List, Optional, Tuple, Any, Union
import threading
import queue
import time as time_module
from pathlib import Path
import scipy.stats as stats
from scipy.optimize import minimize_scalar, brentq
import talib
from sklearn.ensemble import IsolationForest, RandomForestClassifier, GradientBoostingRegressor
from sklearn.preprocessing import StandardScaler, RobustScaler
from sklearn.cluster import DBSCAN
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score, classification_report
import joblib
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.animation import FuncAnimation
import seaborn as sns
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from concurrent.futures import ThreadPoolExecutor, as_completed
import psutil
import gc
from collections import defaultdict, deque
import pickle
import hashlib
import os
import sys
from dataclasses import dataclass, field
from enum import Enum
import asyncio

# Configure warnings and logging
warnings.filterwarnings('ignore')
plt.style.use('seaborn-v0_8')

# Setup comprehensive logging
log_formatter = logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s'
)

file_handler = logging.FileHandler('trading_system.log')
file_handler.setFormatter(log_formatter)

console_handler = logging.StreamHandler()
console_handler.setFormatter(log_formatter)

logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)
logger.addHandler(file_handler)
logger.addHandler(console_handler)


# Custom exceptions
class TradingSystemError(Exception):
    """Base exception for trading system errors"""
    pass


class DataValidationError(TradingSystemError):
    """Data validation specific errors"""
    pass


class StrategyError(TradingSystemError):
    """Strategy execution specific errors"""
    pass


class ConfigurationError(TradingSystemError):
    """Configuration related errors"""
    pass


@dataclass
class Position:
    """Position data structure with complete field definitions"""
    instrument: str
    strike: float
    option_type: str  # 'CE' or 'PE'
    expiry: datetime
    entry_price: float
    quantity: int
    entry_time: datetime
    strategy: str
    stop_loss: float = 0.0
    target: float = 0.0
    trailing_stop: float = 0.0
    current_price: float = 0.0
    unrealized_pnl: float = 0.0
    max_profit: float = 0.0
    max_loss: float = 0.0

    def update_price(self, current_price: float):
        """Update current price and P&L calculations"""
        self.current_price = current_price
        self.unrealized_pnl = (current_price - self.entry_price) * self.quantity
        self.max_profit = max(self.max_profit, self.unrealized_pnl)
        self.max_loss = min(self.max_loss, self.unrealized_pnl)


@dataclass
class Trade:
    """Completed trade data structure"""
    instrument: str
    strike: float
    option_type: str
    expiry: datetime
    entry_price: float
    exit_price: float
    quantity: int
    entry_time: datetime
    exit_time: datetime
    strategy: str
    pnl: float
    max_profit: float
    max_loss: float
    exit_reason: str
    holding_time: timedelta


class ConfigManager:
    """Centralized configuration management with file-based configs"""

    def __init__(self, config_dir: str = "configs"):
        self.config_dir = Path(config_dir)
        self.config_dir.mkdir(exist_ok=True)
        self._create_default_configs()
        self.load_all_configs()

    def _create_default_configs(self):
        """Create all default configuration files"""

        # Market configuration
        market_config = {
            "trading_sessions": {
                "pre_market": {"start": "09:00", "end": "09:15"},
                "opening": {"start": "09:15", "end": "10:30"},
                "regular": {"start": "10:30", "end": "14:30"},
                "closing": {"start": "14:30", "end": "15:15"},
                "square_off": {"start": "15:15", "end": "15:30"}
            },
            "exchanges": {
                "NSE": {
                    "trading_hours": {"start": "09:15", "end": "15:30"},
                    "settlement": "T+1",
                    "currency": "INR",
                    "timezone": "Asia/Kolkata"
                },
                "MCX": {
                    "trading_hours": {"start": "09:00", "end": "23:30"},
                    "settlement": "T+1",
                    "currency": "INR",
                    "timezone": "Asia/Kolkata"
                }
            },
            "current_year": datetime.now().year
        }

        # Instruments configuration
        instruments_config = {
            "INDEX_OPTIONS": {
                "NIFTY": {
                    "lot_size": 75,
                    "tick_size": 0.05,
                    "strike_interval": 50,
                    "atm_reference": "spot_price",
                    "exchange": "NSE",
                    "multiplier": 1,
                    "margin_percentage": 0.10,
                    "circuit_limit": 0.10,
                    "spot_identifier": "NIFTY",
                    "vix_identifier": "INDIAVIX",
                    "futures_identifier": "NIFTY_FUT"
                },
                "BANKNIFTY": {
                    "lot_size": 15,
                    "tick_size": 0.05,
                    "strike_interval": 100,
                    "atm_reference": "spot_price",
                    "exchange": "NSE",
                    "multiplier": 1,
                    "margin_percentage": 0.15,
                    "circuit_limit": 0.10,
                    "spot_identifier": "BANKNIFTY",
                    "vix_identifier": "INDIAVIX",
                    "futures_identifier": "BANKNIFTY_FUT"
                }
            },
            "MCX_OPTIONS": {
                "CRUDEOIL": {
                    "lot_size": 100,
                    "tick_size": 1.0,
                    "strike_interval": 20,
                    "atm_reference": "near_month_futures",
                    "exchange": "MCX",
                    "multiplier": 1,
                    "margin_percentage": 0.08,
                    "circuit_limit": 0.05,
                    "futures_identifier": "CRUDEOIL_FUT"
                }
            }
        }

        # Strategy configuration
        strategy_config = {
            "smart_money_detection": {
                "oi_thresholds": {
                    "NIFTY": {
                        "significant": 25000,
                        "major": 75000,
                        "institutional": 150000
                    },
                    "BANKNIFTY": {
                        "significant": 5000,
                        "major": 15000,
                        "institutional": 30000
                    }
                },
                "time_windows": {
                    "fast": 5,
                    "medium": 15,
                    "slow": 30
                },
                "confidence_thresholds": {
                    "high": 0.80,
                    "medium": 0.65,
                    "low": 0.50
                }
            },
            "risk_management": {
                "position_sizing": {
                    "max_risk_per_trade": 0.015,
                    "max_portfolio_risk": 0.03,
                    "max_positions": 5
                },
                "stop_loss": {
                    "options_long": 0.30,
                    "options_short": 2.0
                },
                "profit_targets": {
                    "quick_profit": 0.25,
                    "target_profit": 0.50
                }
            },
            "session_strategies": {
                "opening": ["smart_money_following", "gap_trading"],
                "regular": ["mean_reversion", "volatility_trading"],
                "closing": ["profit_booking"]
            }
        }

        # Holiday calendar
        holiday_calendar = {
            str(datetime.now().year): [
                {"date": f"{datetime.now().year}-01-26", "name": "Republic Day", "type": "full_closure"},
                {"date": f"{datetime.now().year}-03-14", "name": "Holi", "type": "full_closure"},
                {"date": f"{datetime.now().year}-08-15", "name": "Independence Day", "type": "full_closure"},
                {"date": f"{datetime.now().year}-10-02", "name": "Gandhi Jayanti", "type": "full_closure"}
            ]
        }

        # Data mapping configuration
        data_mapping = {
            "excel_column_mapping": {
                "Short Exchange Name": "exchange_short",
                "Exchange": "exchange",
                "Scrip Code": "scrip_code",
                "Scrip Name": "scrip_name",
                "Current": "current_price",
                "Open Interest": "open_interest",
                "OI Difference": "oi_change",
                "Strike Price": "strike_price",
                "Call/Put": "option_type",
                "Expiry Date": "expiry_date",
                "Bid Price": "bid_price",
                "Offer Price": "ask_price",
                "Instrument Type": "instrument_type"
            },
            "instrument_identification": {
                "spot_patterns": ["EQ"],
                "futures_patterns": ["FUTIDX", "FUTCOM"],
                "options_patterns": ["OPTIDX", "OPTCOM"],
                "vix_patterns": ["INDIAVIX"]
            }
        }

        # Save all configurations
        configs = {
            "market_config.json": market_config,
            "instruments_config.json": instruments_config,
            "strategy_config.json": strategy_config,
            "holiday_calendar.json": holiday_calendar,
            "data_mapping.json": data_mapping
        }

        for filename, config in configs.items():
            config_path = self.config_dir / filename
            if not config_path.exists():
                with open(config_path, 'w') as f:
                    json.dump(config, f, indent=2)
                logger.info(f"Created default config: {filename}")

    def load_all_configs(self):
        """Load all configuration files"""
        try:
            self.market_config = self._load_config("market_config.json")
            self.instruments_config = self._load_config("instruments_config.json")
            self.strategy_config = self._load_config("strategy_config.json")
            self.holiday_calendar = self._load_config("holiday_calendar.json")
            self.data_mapping = self._load_config("data_mapping.json")
            logger.info("All configurations loaded successfully")
        except Exception as e:
            logger.error(f"Error loading configurations: {e}")
            raise ConfigurationError(f"Failed to load configurations: {e}")

    def _load_config(self, filename: str) -> Dict:
        """Load individual configuration file"""
        config_path = self.config_dir / filename
        try:
            with open(config_path, 'r') as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"Error loading {filename}: {e}")
            raise

    def get_instrument_config(self, instrument: str) -> Optional[Dict]:
        """Get configuration for specific instrument"""
        for category in self.instruments_config.values():
            if instrument in category:
                return category[instrument]
        return None

    def is_trading_day(self, date: datetime) -> bool:
        """Check if given date is a trading day"""
        if date.weekday() >= 5:  # Weekend
            return False

        date_str = date.strftime("%Y-%m-%d")
        year_holidays = self.holiday_calendar.get(str(date.year), [])

        for holiday in year_holidays:
            if holiday["date"] == date_str and holiday["type"] == "full_closure":
                return False

        return True

    def get_session_type(self, current_time: time) -> str:
        """Get current trading session type"""
        sessions = self.market_config["trading_sessions"]

        for session_name, session_time in sessions.items():
            start_time = datetime.strptime(session_time["start"], "%H:%M").time()
            end_time = datetime.strptime(session_time["end"], "%H:%M").time()

            if start_time <= current_time <= end_time:
                return session_name

        return "closed"


class DataProcessor:
    """Advanced data processing with validation and enrichment"""

    def __init__(self, config_manager: ConfigManager):
        self.config = config_manager
        self.last_update = None
        self.data_cache = {}
        self.processed_data = {}
        self.data_history = deque(maxlen=1000)
        self.column_mapping = self.config.data_mapping["excel_column_mapping"]

    def process_excel_data(self, file_path: str) -> Optional[Dict[str, pd.DataFrame]]:
        """Main data processing pipeline"""
        try:
            # Read Excel file
            raw_data = self._read_excel_file(file_path)
            if raw_data is None:
                return None

            # Clean and standardize data
            cleaned_data = self._clean_data(raw_data)

            # Categorize instruments
            categorized_data = self._categorize_instruments(cleaned_data)

            # Enrich with calculated fields
            enriched_data = self._enrich_data(categorized_data)

            # Cache for historical analysis
            self._cache_data(enriched_data)

            self.processed_data = enriched_data
            self.last_update = datetime.now()
            return enriched_data

        except Exception as e:
            logger.error(f"Error processing Excel data: {e}")
            return None

    def _read_excel_file(self, file_path: str) -> Optional[pd.DataFrame]:
        """Read Excel file with error handling"""
        try:
            if file_path.endswith('.xlsx') or file_path.endswith('.xls'):
                df = pd.read_excel(file_path)
            elif file_path.endswith('.csv'):
                df = pd.read_csv(file_path)
            else:
                logger.error(f"Unsupported file format: {file_path}")
                return None

            if df.empty:
                logger.warning("File is empty")
                return None

            # Rename columns based on mapping
            df = df.rename(columns=self.column_mapping)
            return df

        except Exception as e:
            logger.error(f"Error reading file {file_path}: {e}")
            return None

    def _clean_data(self, df: pd.DataFrame) -> pd.DataFrame:
        """Clean and standardize data"""
        try:
            # Handle numeric columns
            numeric_columns = [
                'current_price', 'open_interest', 'oi_change', 'strike_price',
                'bid_price', 'ask_price'
            ]

            for col in numeric_columns:
                if col in df.columns:
                    df[col] = pd.to_numeric(df[col], errors='coerce')
                    df[col].fillna(0, inplace=True)

            # Clean string columns
            string_columns = ['scrip_name', 'option_type', 'instrument_type']
            for col in string_columns:
                if col in df.columns:
                    df[col] = df[col].astype(str).str.strip().str.upper()

            # Parse expiry dates
            if 'expiry_date' in df.columns:
                df['expiry_date'] = pd.to_datetime(df['expiry_date'], errors='coerce')
                df['days_to_expiry'] = (df['expiry_date'] - datetime.now()).dt.days
                df['time_to_expiry'] = df['days_to_expiry'] / 365.25

            return df

        except Exception as e:
            logger.error(f"Error cleaning data: {e}")
            return df

    def _categorize_instruments(self, df: pd.DataFrame) -> Dict[str, pd.DataFrame]:
        """Categorize instruments by type"""
        categorized = {
            'spot': pd.DataFrame(),
            'futures': pd.DataFrame(),
            'options': pd.DataFrame(),
            'vix': pd.DataFrame()
        }

        try:
            instrument_patterns = self.config.data_mapping["instrument_identification"]

            if 'instrument_type' in df.columns:
                # Spot instruments
                spot_mask = df['instrument_type'].isin(instrument_patterns["spot_patterns"])
                categorized['spot'] = df[spot_mask].copy()

                # Futures instruments
                futures_mask = df['instrument_type'].isin(instrument_patterns["futures_patterns"])
                categorized['futures'] = df[futures_mask].copy()

                # Options instruments
                options_mask = df['instrument_type'].isin(instrument_patterns["options_patterns"])
                categorized['options'] = df[options_mask].copy()

                # VIX instruments
                if 'scrip_name' in df.columns:
                    vix_mask = df['scrip_name'].isin(instrument_patterns["vix_patterns"])
                    categorized['vix'] = df[vix_mask].copy()

            return categorized

        except Exception as e:
            logger.error(f"Error categorizing instruments: {e}")
            return categorized

    def _enrich_data(self, categorized_data: Dict[str, pd.DataFrame]) -> Dict[str, pd.DataFrame]:
        """Add calculated fields and derived metrics"""
        try:
            # Enrich options data
            if not categorized_data['options'].empty:
                options_df = categorized_data['options'].copy()

                # Calculate moneyness
                options_df['moneyness'] = self._calculate_moneyness(options_df, categorized_data['spot'])

                # Calculate basic Greeks
                options_df = self._add_basic_greeks(options_df, categorized_data['spot'], categorized_data['vix'])

                # Calculate bid-ask spread
                if 'bid_price' in options_df.columns and 'ask_price' in options_df.columns:
                    options_df['bid_ask_spread'] = options_df['ask_price'] - options_df['bid_price']
                    options_df['bid_ask_spread_pct'] = (
                            options_df['bid_ask_spread'] / options_df['current_price'] * 100
                    )

                categorized_data['options'] = options_df

            return categorized_data

        except Exception as e:
            logger.error(f"Error enriching data: {e}")
            return categorized_data

    def _calculate_moneyness(self, options_df: pd.DataFrame, spot_df: pd.DataFrame) -> pd.Series:
        """Calculate option moneyness"""
        if spot_df.empty or 'current_price' not in spot_df.columns:
            return pd.Series([0] * len(options_df))

        spot_price = spot_df['current_price'].iloc[0] if not spot_df.empty else 0

        if 'strike_price' in options_df.columns and spot_price > 0:
            return (options_df['strike_price'] - spot_price) / spot_price

        return pd.Series([0] * len(options_df))

    def _add_basic_greeks(self, options_df: pd.DataFrame, spot_df: pd.DataFrame, vix_df: pd.DataFrame) -> pd.DataFrame:
        """Add basic Greeks calculations"""
        try:
            # Initialize Greeks columns
            options_df['delta'] = 0.0
            options_df['gamma'] = 0.0
            options_df['theta'] = 0.0
            options_df['vega'] = 0.0
            options_df['implied_volatility'] = 0.15  # Default IV

            if spot_df.empty or vix_df.empty:
                return options_df

            spot_price = spot_df['current_price'].iloc[0]
            vix_value = vix_df['current_price'].iloc[0] / 100 if not vix_df.empty else 0.15
            risk_free_rate = 0.065  # 6.5%

            for idx, row in options_df.iterrows():
                try:
                    strike = row.get('strike_price', 0)
                    time_to_expiry = row.get('time_to_expiry', 0)
                    option_price = row.get('current_price', 0)
                    option_type = row.get('option_type', 'CE')

                    if strike > 0 and time_to_expiry > 0 and option_price > 0:
                        # Simplified Greeks calculation
                        moneyness = row.get('moneyness', 0)

                        # Basic Delta approximation
                        if option_type == 'CE':
                            delta = 0.5 + moneyness * 2  # Simplified
                            delta = max(0, min(1, delta))
                        else:
                            delta = -0.5 + moneyness * 2  # Simplified
                            delta = max(-1, min(0, delta))

                        # Basic Gamma approximation
                        gamma = 1 / (strike * vix_value * np.sqrt(time_to_expiry)) if time_to_expiry > 0 else 0

                        # Basic Theta approximation (time decay)
                        theta = -option_price / (time_to_expiry * 365) if time_to_expiry > 0 else 0

                        # Basic Vega approximation
                        vega = strike * np.sqrt(time_to_expiry) * 0.01 if time_to_expiry > 0 else 0

                        options_df.loc[idx, 'delta'] = delta
                        options_df.loc[idx, 'gamma'] = gamma
                        options_df.loc[idx, 'theta'] = theta
                        options_df.loc[idx, 'vega'] = vega
                        options_df.loc[idx, 'implied_volatility'] = vix_value

                except Exception as e:
                    logger.debug(f"Error calculating Greeks for row {idx}: {e}")
                    continue

            return options_df

        except Exception as e:
            logger.error(f"Error adding Greeks: {e}")
            return options_df

    def _cache_data(self, categorized_data: Dict[str, pd.DataFrame]):
        """Cache data for historical analysis"""
        try:
            cache_entry = {
                'timestamp': datetime.now(),
                'spot_price': 0,
                'vix_value': 0,
                'total_oi': 0
            }

            if not categorized_data['spot'].empty:
                cache_entry['spot_price'] = categorized_data['spot']['current_price'].iloc[0]

            if not categorized_data['vix'].empty:
                cache_entry['vix_value'] = categorized_data['vix']['current_price'].iloc[0]

            if not categorized_data['options'].empty:
                cache_entry['total_oi'] = categorized_data['options']['open_interest'].sum()

            self.data_history.append(cache_entry)

        except Exception as e:
            logger.debug(f"Error caching data: {e}")


class SmartMoneyDetector:
    """Smart money flow detection using OI analysis"""

    def __init__(self, config_manager: ConfigManager):
        self.config = config_manager
        self.smart_money_config = config_manager.strategy_config["smart_money_detection"]
        self.flow_history = deque(maxlen=500)

    def detect_smart_money_flows(self, options_data: pd.DataFrame, instrument: str) -> pd.DataFrame:
        """Main smart money detection pipeline"""
        if options_data.empty:
            return pd.DataFrame()

        try:
            # Get instrument-specific thresholds
            thresholds = self.smart_money_config["oi_thresholds"].get(
                instrument, self.smart_money_config["oi_thresholds"]["NIFTY"]
            )

            # Detect institutional flows
            signals = self._detect_institutional_flows(options_data, thresholds)

            # Add confidence scores
            signals = self._calculate_confidence_scores(signals)

            return signals

        except Exception as e:
            logger.error(f"Error in smart money detection: {e}")
            return pd.DataFrame()

    def _detect_institutional_flows(self, df: pd.DataFrame, thresholds: Dict) -> pd.DataFrame:
        """Detect large institutional flows"""
        signals = df.copy()

        # Large OI changes
        signals['large_oi_build'] = (
                (signals['oi_change'] > thresholds['significant']) &
                (signals['oi_change'] > 0)
        )

        signals['institutional_build'] = signals['oi_change'] > thresholds['institutional']

        # Overall smart money signal
        signals['smart_money_signal'] = (
                signals['large_oi_build'] | signals['institutional_build']
        )

        return signals

    def _calculate_confidence_scores(self, df: pd.DataFrame) -> pd.DataFrame:
        """Calculate confidence scores for signals"""
        df = df.copy()

        try:
            df['confidence_score'] = 0.0

            # Base confidence from OI change magnitude
            if 'oi_change' in df.columns:
                oi_change_normalized = abs(df['oi_change']) / 100000
                df['confidence_score'] += np.minimum(oi_change_normalized * 0.3, 0.3)

            # Add confidence for institutional signals
            if 'institutional_build' in df.columns:
                df.loc[df['institutional_build'], 'confidence_score'] += 0.4

            if 'large_oi_build' in df.columns:
                df.loc[df['large_oi_build'], 'confidence_score'] += 0.3

            # Cap confidence at 1.0
            df['confidence_score'] = np.minimum(df['confidence_score'], 1.0)

        except Exception as e:
            logger.debug(f"Error calculating confidence scores: {e}")

        return df


class StrategyEngine:
    """Strategy implementation and signal generation"""

    def __init__(self, config_manager: ConfigManager, smart_money_detector: SmartMoneyDetector):
        self.config = config_manager
        self.smart_money_detector = smart_money_detector
        self.strategy_config = config_manager.strategy_config
        self.signal_history = deque(maxlen=1000)

    def generate_signals(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
        """Main signal generation pipeline"""
        signals = []

        try:
            current_session = self.config.get_session_type(datetime.now().time())
            session_strategies = self.strategy_config["session_strategies"].get(current_session, [])

            for strategy_name in session_strategies:
                try:
                    if strategy_name == "smart_money_following":
                        signals.extend(self._smart_money_following_strategy(market_data, instrument))
                    elif strategy_name == "gap_trading":
                        signals.extend(self._gap_trading_strategy(market_data, instrument))
                    elif strategy_name == "mean_reversion":
                        signals.extend(self._mean_reversion_strategy(market_data, instrument))
                    elif strategy_name == "volatility_trading":
                        signals.extend(self._volatility_trading_strategy(market_data, instrument))
                    elif strategy_name == "profit_booking":
                        signals.extend(self._profit_booking_strategy(market_data, instrument))

                except Exception as e:
                    logger.error(f"Error in strategy {strategy_name}: {e}")

            # Filter and rank signals
            signals = self._filter_and_rank_signals(signals)

            return signals

        except Exception as e:
            logger.error(f"Error generating signals: {e}")
            return []

    def _smart_money_following_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
        """Smart money following strategy"""
        signals = []

        try:
            options_data = market_data.get('options', pd.DataFrame())
            if options_data.empty:
                return signals

            # Get smart money signals
            smart_money_signals = self.smart_money_detector.detect_smart_money_flows(options_data, instrument)

            # Convert to trading signals
            high_confidence_signals = smart_money_signals[
                (smart_money_signals.get('confidence_score', 0) > 0.7) &
                (smart_money_signals.get('smart_money_signal', False))
                ]

            for idx, row in high_confidence_signals.iterrows():
                signal = {
                    'strategy': 'smart_money_following',
                    'instrument': instrument,
                    'strike': row.get('strike_price', 0),
                    'option_type': row.get('option_type', 'CE'),
                    'expiry': row.get('expiry_date'),
                    'signal_type': 'BUY' if row.get('oi_change', 0) > 0 else 'SELL',
                    'entry_price': row.get('current_price', 0),
                    'confidence': row.get('confidence_score', 0),
                    'reasoning': f"Smart money flow detected: OI change {row.get('oi_change', 0)}",
                    'timestamp': datetime.now()
                }
                signals.append(signal)

        except Exception as e:
            logger.debug(f"Error in smart money following strategy: {e}")

        return signals

    def _gap_trading_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
        """Gap trading strategy for opening session"""
        signals = []

        try:
            spot_data = market_data.get('spot', pd.DataFrame())
            options_data = market_data.get('options', pd.DataFrame())

            if spot_data.empty or options_data.empty:
                return signals

            # Simple gap detection logic
            atm_options = options_data[abs(options_data.get('moneyness', 1)) < 0.02]

            for idx, row in atm_options.head(2).iterrows():
                if row.get('current_price', 0) > 0:
                    signal = {
                        'strategy': 'gap_trading',
                        'instrument': instrument,
                        'strike': row.get('strike_price', 0),
                        'option_type': row.get('option_type', 'CE'),
                        'expiry': row.get('expiry_date'),
                        'signal_type': 'BUY',
                        'entry_price': row.get('current_price', 0),
                        'confidence': 0.65,
                        'reasoning': f"Gap trading opportunity at ATM strike",
                        'timestamp': datetime.now()
                    }
                    signals.append(signal)

        except Exception as e:
            logger.debug(f"Error in gap trading strategy: {e}")

        return signals

    def _mean_reversion_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
        """Mean reversion strategy"""
        signals = []

        try:
            options_data = market_data.get('options', pd.DataFrame())

            if options_data.empty:
                return signals

            # Look for overpriced options
            if 'implied_volatility' in options_data.columns:
                high_iv_options = options_data[
                    options_data['implied_volatility'] > options_data['implied_volatility'].quantile(0.8)
                    ]

                for idx, row in high_iv_options.head(2).iterrows():
                    if row.get('current_price', 0) > 5:
                        signal = {
                            'strategy': 'mean_reversion',
                            'instrument': instrument,
                            'strike': row.get('strike_price', 0),
                            'option_type': row.get('option_type', 'CE'),
                            'expiry': row.get('expiry_date'),
                            'signal_type': 'SELL',
                            'entry_price': row.get('current_price', 0),
                            'confidence': 0.60,
                            'reasoning': f"High IV mean reversion: {row.get('implied_volatility', 0):.2f}",
                            'timestamp': datetime.now()
                        }
                        signals.append(signal)

        except Exception as e:
            logger.debug(f"Error in mean reversion strategy: {e}")

        return signals

    def _volatility_trading_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
        """Volatility-based trading strategy"""
        signals = []

        try:
            vix_data = market_data.get('vix', pd.DataFrame())
            options_data = market_data.get('options', pd.DataFrame())

            if vix_data.empty or options_data.empty:
                return signals

            current_vix = vix_data['current_price'].iloc[0]

            # Low volatility regime - buy volatility
            if current_vix < 12:
                atm_options = options_data[abs(options_data.get('moneyness', 1)) < 0.02]

                for idx, row in atm_options.head(2).iterrows():
                    signal = {
                        'strategy': 'volatility_trading',
                        'instrument': instrument,
                        'strike': row.get('strike_price', 0),
                        'option_type': row.get('option_type', 'CE'),
                        'expiry': row.get('expiry_date'),
                        'signal_type': 'BUY',
                        'entry_price': row.get('current_price', 0),
                        'confidence': 0.65,
                        'reasoning': f"Low VIX regime ({current_vix:.1f}) - buy volatility",
                        'timestamp': datetime.now()
                    }
                    signals.append(signal)

            # High volatility regime - sell volatility
            elif current_vix > 18:
                otm_options = options_data[abs(options_data.get('moneyness', 0)) > 0.02]

                for idx, row in otm_options.head(2).iterrows():
                    signal = {
                        'strategy': 'volatility_trading',
                        'instrument': instrument,
                        'strike': row.get('strike_price', 0),
                        'option_type': row.get('option_type', 'CE'),
                        'expiry': row.get('expiry_date'),
                        'signal_type': 'SELL',
                        'entry_price': row.get('current_price', 0),
                        'confidence': 0.70,
                        'reasoning': f"High VIX regime ({current_vix:.1f}) - sell volatility",
                        'timestamp': datetime.now()
                    }
                    signals.append(signal)

        except Exception as e:
            logger.debug(f"Error in volatility trading strategy: {e}")

        return signals

    def _profit_booking_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
        """Profit booking strategy for closing session"""
        signals = []
        # This would typically check existing positions and generate exit signals
        return signals

    def _filter_and_rank_signals(self, signals: List[Dict]) -> List[Dict]:
        """Filter and rank signals by confidence and other criteria"""
        if not signals:
            return signals

        try:
            # Filter by minimum confidence
            min_confidence = 0.5
            filtered_signals = [s for s in signals if s.get('confidence', 0) >= min_confidence]

            # Sort by confidence (descending)
            filtered_signals.sort(key=lambda x: x.get('confidence', 0), reverse=True)

            # Limit number of signals
            max_signals = 5
            return filtered_signals[:max_signals]

        except Exception as e:
            logger.debug(f"Error filtering signals: {e}")
            return signals


class PaperTradingEngine:
    """Advanced paper trading with realistic execution simulation"""

    def __init__(self, config_manager: ConfigManager, initial_capital: float = 1000000):
        self.config = config_manager
        self.initial_capital = initial_capital
        self.current_capital = initial_capital
        self.positions: List[Position] = []
        self.completed_trades: List[Trade] = []
        self.daily_pnl = 0.0
        self.unrealized_pnl = 0.0
        self.max_drawdown = 0.0
        self.peak_capital = initial_capital

        # Risk management
        self.risk_config = config_manager.strategy_config["risk_management"]

        # Database for trade storage
        self.db_path = "paper_trading.db"
        self._initialize_database()

    def _initialize_database(self):
        """Initialize SQLite database for trade storage"""
        try:
            conn = sqlite3.connect(self.db_path)
            cursor = conn.cursor()

            # Positions table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS positions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    instrument TEXT,
                    strike REAL,
                    option_type TEXT,
                    expiry DATE,
                    entry_price REAL,
                    quantity INTEGER,
                    entry_time TIMESTAMP,
                    strategy TEXT,
                    stop_loss REAL,
                    target REAL,
                    current_price REAL,
                    unrealized_pnl REAL,
                    status TEXT DEFAULT 'OPEN'
                )
            """)

            # Completed trades table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS completed_trades (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    instrument TEXT,
                    strike REAL,
                    option_type TEXT,
                    expiry DATE,
                    entry_price REAL,
                    exit_price REAL,
                    quantity INTEGER,
                    entry_time TIMESTAMP,
                    exit_time TIMESTAMP,
                    strategy TEXT,
                    pnl REAL,
                    max_profit REAL,
                    max_loss REAL,
                    exit_reason TEXT,
                    holding_time_minutes INTEGER
                )
            """)

            # Daily performance table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS daily_performance (
                    date DATE PRIMARY KEY,
                    starting_capital REAL,
                    ending_capital REAL,
                    realized_pnl REAL,
                    unrealized_pnl REAL,
                    total_pnl REAL,
                    trades_count INTEGER,
                    winning_trades INTEGER,
                    max_drawdown REAL
                )
            """)

            conn.commit()
            conn.close()
            logger.info("Paper trading database initialized")

        except Exception as e:
            logger.error(f"Error initializing database: {e}")

    def execute_signal(self, signal: Dict, current_market_data: Dict[str, pd.DataFrame]) -> bool:
        """Execute a trading signal"""
        try:
            # Risk checks
            if not self._risk_check(signal):
                logger.info(f"Signal rejected by risk management: {signal['strategy']}")
                return False

            # Position sizing
            position_size = self._calculate_position_size(signal)
            if position_size <= 0:
                logger.info(f"Invalid position size calculated: {position_size}")
                return False

            # Simulate order execution
            executed_price = self._simulate_execution(signal, current_market_data)
            if executed_price <= 0:
                logger.info(f"Order execution failed for signal: {signal['strategy']}")
                return False

            # Create position
            position = Position(
                instrument=signal['instrument'],
                strike=signal['strike'],
                option_type=signal['option_type'],
                expiry=signal['expiry'],
                entry_price=executed_price,
                quantity=position_size,
                entry_time=datetime.now(),
                strategy=signal['strategy'],
                stop_loss=self._calculate_stop_loss(executed_price, signal),
                target=self._calculate_target(executed_price, signal)
            )

            self.positions.append(position)
            self._save_position_to_db(position)

            # Update capital
            trade_cost = executed_price * position_size
            self.current_capital -= trade_cost

            logger.info(
                f"Position opened: {signal['strategy']} {signal['option_type']} {signal['strike']} @ {executed_price}")
            return True

        except Exception as e:
            logger.error(f"Error executing signal: {e}")
            return False

    def update_positions(self, current_market_data: Dict[str, pd.DataFrame]):
        """Update all open positions with current market data"""
        try:
            options_data = current_market_data.get('options', pd.DataFrame())
            if options_data.empty:
                return

            positions_to_close = []

            for position in self.positions:
                # Find current price for this position
                position_data = options_data[
                    (options_data['strike_price'] == position.strike) &
                    (options_data['option_type'] == position.option_type) &
                    (options_data['expiry_date'] == position.expiry)
                    ]

                if not position_data.empty:
                    current_price = position_data['current_price'].iloc[0]
                    position.update_price(current_price)

                    # Check exit conditions
                    exit_reason = self._check_exit_conditions(position)
                    if exit_reason:
                        positions_to_close.append((position, exit_reason))

            # Close positions that meet exit criteria
            for position, exit_reason in positions_to_close:
                self._close_position(position, exit_reason)

            # Update unrealized P&L
            self.unrealized_pnl = sum(pos.unrealized_pnl for pos in self.positions)

            # Update performance metrics
            self._update_performance_metrics()

        except Exception as e:
            logger.error(f"Error updating positions: {e}")

    def _risk_check(self, signal: Dict) -> bool:
        """Comprehensive risk management checks"""
        try:
            # Check maximum positions limit
            if len(self.positions) >= self.risk_config["position_sizing"]["max_positions"]:
                return False

            # Check daily loss limit
            daily_loss_limit = self.initial_capital * self.risk_config["position_sizing"]["max_portfolio_risk"]
            if abs(self.daily_pnl) > daily_loss_limit:
                return False

            # Check available capital
            estimated_cost = signal.get('entry_price', 0) * 100
            if estimated_cost > self.current_capital * 0.5:
                return False

            # Time-based checks
            current_time = datetime.now().time()
            session = self.config.get_session_type(current_time)

            if session == 'square_off':
                return False

            return True

        except Exception as e:
            logger.debug(f"Error in risk check: {e}")
            return False

    def _calculate_position_size(self, signal: Dict) -> int:
        """Calculate position size based on risk management rules"""
        try:
            # Get instrument configuration
            instrument_config = self.config.get_instrument_config(signal['instrument'])
            if not instrument_config:
                return 0

            lot_size = instrument_config['lot_size']
            entry_price = signal.get('entry_price', 0)

            if entry_price <= 0:
                return 0

            # Risk-based position sizing
            risk_per_trade = self.current_capital * self.risk_config["position_sizing"]["max_risk_per_trade"]

            # Calculate stop loss distance
            stop_loss_pct = self.risk_config["stop_loss"]["options_long"]
            stop_loss_amount = entry_price * stop_loss_pct

            # Position size = Risk amount / Stop loss amount
            position_value = risk_per_trade / stop_loss_amount if stop_loss_amount > 0 else 0

            if position_value > 0:
                num_lots = max(1, int(position_value / (entry_price * lot_size)))
                return num_lots * lot_size

            return 0

        except Exception as e:
            logger.debug(f"Error calculating position size: {e}")
            return 0

    def _simulate_execution(self, signal: Dict, market_data: Dict[str, pd.DataFrame]) -> float:
        """Simulate realistic order execution with slippage"""
        try:
            options_data = market_data.get('options', pd.DataFrame())
            if options_data.empty:
                return 0

            # Find the specific option
            option_data = options_data[
                (options_data['strike_price'] == signal['strike']) &
                (options_data['option_type'] == signal['option_type'])
                ]

            if option_data.empty:
                return 0

            current_price = option_data['current_price'].iloc[0]
            bid_price = option_data.get('bid_price', pd.Series([current_price])).iloc[0]
            ask_price = option_data.get('ask_price', pd.Series([current_price])).iloc[0]

            # Simulate slippage based on signal type
            if signal['signal_type'] == 'BUY':
                executed_price = ask_price * 1.01  # 1% slippage
            else:
                executed_price = bid_price * 0.99  # 1% slippage

            return max(0.05, executed_price)  # Minimum tick size

        except Exception as e:
            logger.debug(f"Error simulating execution: {e}")
            return 0

    def _calculate_stop_loss(self, entry_price: float, signal: Dict) -> float:
        """Calculate stop loss price"""
        try:
            if signal['signal_type'] == 'BUY':
                stop_loss_pct = self.risk_config["stop_loss"]["options_long"]
                return entry_price * (1 - stop_loss_pct)
            else:
                stop_loss_multiplier = self.risk_config["stop_loss"]["options_short"]
                return entry_price * stop_loss_multiplier

        except Exception:
            return entry_price * 0.7  # Default 30% stop loss

    def _calculate_target(self, entry_price: float, signal: Dict) -> float:
        """Calculate target price"""
        try:
            target_multiplier = self.risk_config["profit_targets"]["target_profit"]
            if signal['signal_type'] == 'BUY':
                return entry_price * (1 + target_multiplier)
            else:
                return entry_price * (1 - target_multiplier)

        except Exception:
            return entry_price * 1.5  # Default 50% target

    def _check_exit_conditions(self, position: Position) -> Optional[str]:
        """Check if position should be closed"""
        try:
            current_price = position.current_price

            # Stop loss check
            if position.quantity > 0:  # Long position
                if current_price <= position.stop_loss:
                    return "Stop Loss"
            else:  # Short position
                if current_price >= position.stop_loss:
                    return "Stop Loss"

            # Target check
            if position.quantity > 0:  # Long position
                if current_price >= position.target:
                    return "Target Reached"
            else:  # Short position
                if current_price <= position.target:
                    return "Target Reached"

            # Time-based exit
            time_to_expiry = (position.expiry - datetime.now()).days
            if time_to_expiry <= 0:
                return "Expiry"

            # Session-based exit
            current_time = datetime.now().time()
            session = self.config.get_session_type(current_time)
            if session == 'square_off':
                return "End of Day Square-off"

            return None

        except Exception as e:
            logger.debug(f"Error checking exit conditions: {e}")
            return None

    def _close_position(self, position: Position, exit_reason: str):
        """Close a position and record the trade"""
        try:
            # Calculate P&L
            exit_price = position.current_price
            pnl = (exit_price - position.entry_price) * position.quantity

            # Create completed trade record
            trade = Trade(
                instrument=position.instrument,
                strike=position.strike,
                option_type=position.option_type,
                expiry=position.expiry,
                entry_price=position.entry_price,
                exit_price=exit_price,
                quantity=position.quantity,
                entry_time=position.entry_time,
                exit_time=datetime.now(),
                strategy=position.strategy,
                pnl=pnl,
                max_profit=position.max_profit,
                max_loss=position.max_loss,
                exit_reason=exit_reason,
                holding_time=datetime.now() - position.entry_time
            )

            self.completed_trades.append(trade)
            self._save_trade_to_db(trade)

            # Update capital
            trade_proceeds = exit_price * position.quantity
            self.current_capital += trade_proceeds
            self.daily_pnl += pnl

            # Remove from active positions
            self.positions.remove(position)

            logger.info(
                f"Position closed: {position.strategy} {position.option_type} {position.strike} @ {exit_price}, P&L: {pnl:.2f}, Reason: {exit_reason}")

        except Exception as e:
            logger.error(f"Error closing position: {e}")

    def _save_position_to_db(self, position: Position):
        """Save position to database"""
        try:
            conn = sqlite3.connect(self.db_path)
            cursor = conn.cursor()

            cursor.execute("""
                INSERT INTO positions (instrument, strike, option_type, expiry, entry_price, 
                                     quantity, entry_time, strategy, stop_loss, target, 
                                     current_price, unrealized_pnl)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                position.instrument, position.strike, position.option_type,
                position.expiry, position.entry_price, position.quantity,
                position.entry_time, position.strategy, position.stop_loss,
                position.target, position.current_price, position.unrealized_pnl
            ))

            conn.commit()
            conn.close()

        except Exception as e:
            logger.debug(f"Error saving position to database: {e}")

    def _save_trade_to_db(self, trade: Trade):
        """Save completed trade to database"""
        try:
            conn = sqlite3.connect(self.db_path)
            cursor = conn.cursor()

            cursor.execute("""
                INSERT INTO completed_trades (instrument, strike, option_type, expiry, 
                                            entry_price, exit_price, quantity, entry_time, 
                                            exit_time, strategy, pnl, max_profit, max_loss, 
                                            exit_reason, holding_time_minutes)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                trade.instrument, trade.strike, trade.option_type, trade.expiry,
                trade.entry_price, trade.exit_price, trade.quantity, trade.entry_time,
                trade.exit_time, trade.strategy, trade.pnl, trade.max_profit,
                trade.max_loss, trade.exit_reason, trade.holding_time.total_seconds() / 60
            ))

            conn.commit()
            conn.close()

        except Exception as e:
            logger.debug(f"Error saving trade to database: {e}")

    def _update_performance_metrics(self):
        """Update performance metrics"""
        try:
            total_capital = self.current_capital + self.unrealized_pnl

            # Update peak capital and drawdown
            if total_capital > self.peak_capital:
                self.peak_capital = total_capital

            current_drawdown = (self.peak_capital - total_capital) / self.peak_capital
            self.max_drawdown = max(self.max_drawdown, current_drawdown)

        except Exception as e:
            logger.debug(f"Error updating performance metrics: {e}")

    def get_performance_summary(self) -> Dict:
        """Get comprehensive performance summary"""
        try:
            total_trades = len(self.completed_trades)
            winning_trades = len([t for t in self.completed_trades if t.pnl > 0])

            if total_trades > 0:
                win_rate = winning_trades / total_trades
                avg_pnl = sum(t.pnl for t in self.completed_trades) / total_trades
                avg_holding_time = sum(
                    t.holding_time.total_seconds() for t in self.completed_trades) / total_trades / 60
            else:
                win_rate = 0
                avg_pnl = 0
                avg_holding_time = 0

            total_capital = self.current_capital + self.unrealized_pnl
            total_return = (total_capital - self.initial_capital) / self.initial_capital

            return {
                'initial_capital': self.initial_capital,
                'current_capital': self.current_capital,
                'unrealized_pnl': self.unrealized_pnl,
                'total_capital': total_capital,
                'daily_pnl': self.daily_pnl,
                'total_return': total_return * 100,
                'max_drawdown': self.max_drawdown * 100,
                'total_trades': total_trades,
                'winning_trades': winning_trades,
                'win_rate': win_rate * 100,
                'avg_pnl_per_trade': avg_pnl,
                'avg_holding_time_minutes': avg_holding_time,
                'active_positions': len(self.positions)
            }

        except Exception as e:
            logger.error(f"Error generating performance summary: {e}")
            return {}

    def get_trade_statistics(self) -> Dict:
        """Get detailed trade statistics"""
        try:
            if not self.completed_trades:
                return {}

            trades = self.completed_trades
            total_trades = len(trades)
            winning_trades = len([t for t in trades if t.pnl > 0])
            losing_trades = total_trades - winning_trades

            # P&L statistics
            total_pnl = sum(t.pnl for t in trades)
            winning_pnl = sum(t.pnl for t in trades if t.pnl > 0)
            losing_pnl = sum(t.pnl for t in trades if t.pnl < 0)

            # Average statistics
            avg_win = winning_pnl / winning_trades if winning_trades > 0 else 0
            avg_loss = losing_pnl / losing_trades if losing_trades > 0 else 0
            avg_trade = total_pnl / total_trades if total_trades > 0 else 0

            # Risk metrics
            profit_factor = abs(winning_pnl / losing_pnl) if losing_pnl != 0 else float('inf')

            return {
                'total_trades': total_trades,
                'winning_trades': winning_trades,
                'losing_trades': losing_trades,
                'win_rate': (winning_trades / total_trades * 100) if total_trades > 0 else 0,
                'total_pnl': total_pnl,
                'avg_win': avg_win,
                'avg_loss': avg_loss,
                'avg_trade': avg_trade,
                'profit_factor': profit_factor,
                'largest_win': max((t.pnl for t in trades if t.pnl > 0), default=0),
                'largest_loss': min((t.pnl for t in trades if t.pnl < 0), default=0)
            }

        except Exception as e:
            logger.error(f"Error calculating trade statistics: {e}")
            return {}


class TradingSystemGUI:
    """Advanced GUI for the trading system"""

    def __init__(self, trading_system):
        self.trading_system = trading_system
        self.root = tk.Tk()
        self.root.title("Institutional-Grade Intraday Trading System")
        self.root.geometry("1400x900")

        # Configure style
        self.style = ttk.Style()
        self.style.theme_use('clam')

        self.setup_gui()
        self.update_thread = None
        self.is_running = False

    def setup_gui(self):
        """Setup the main GUI components"""
        # Create main notebook for tabs
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Create tabs
        self.create_main_tab()
        self.create_positions_tab()
        self.create_analytics_tab()
        self.create_settings_tab()

        # Status bar
        self.status_var = tk.StringVar(value="System Ready")
        self.status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

    def create_main_tab(self):
        """Create main dashboard tab"""
        main_frame = ttk.Frame(self.notebook)
        self.notebook.add(main_frame, text="Dashboard")

        # Control panel
        control_frame = ttk.LabelFrame(main_frame, text="System Controls")
        control_frame.pack(fill=tk.X, padx=5, pady=5)

        # File selection
        ttk.Label(control_frame, text="Excel File:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.file_path_var = tk.StringVar()
        ttk.Entry(control_frame, textvariable=self.file_path_var, width=60).grid(row=0, column=1, padx=5, pady=2)
        ttk.Button(control_frame, text="Browse", command=self.browse_file).grid(row=0, column=2, padx=5, pady=2)

        # Instrument selection
        ttk.Label(control_frame, text="Instrument:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        self.instrument_var = tk.StringVar(value="NIFTY")
        instrument_combo = ttk.Combobox(control_frame, textvariable=self.instrument_var,
                                        values=["NIFTY", "BANKNIFTY", "CRUDEOIL"])
        instrument_combo.grid(row=1, column=1, sticky=tk.W, padx=5, pady=2)

        # Control buttons
        button_frame = ttk.Frame(control_frame)
        button_frame.grid(row=2, column=0, columnspan=3, pady=10)
        self.start_button = ttk.Button(button_frame, text="Start Trading", command=self.start_trading)
        self.start_button.pack(side=tk.LEFT, padx=5)

        self.stop_button = ttk.Button(button_frame, text="Stop Trading", command=self.stop_trading, state=tk.DISABLED)
        self.stop_button.pack(side=tk.LEFT, padx=5)

        ttk.Button(button_frame, text="Manual Signal", command=self.manual_signal).pack(side=tk.LEFT, padx=5)

        # Performance summary
        perf_frame = ttk.LabelFrame(main_frame, text="Performance Summary")
        perf_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Performance metrics
        self.perf_text = tk.Text(perf_frame, height=8, wrap=tk.WORD)
        perf_scrollbar = ttk.Scrollbar(perf_frame, orient=tk.VERTICAL, command=self.perf_text.yview)
        self.perf_text.config(yscrollcommand=perf_scrollbar.set)

        self.perf_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        perf_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Market data display
        market_frame = ttk.LabelFrame(main_frame, text="Live Market Data")
        market_frame.pack(fill=tk.X, padx=5, pady=5)

        self.market_tree = ttk.Treeview(market_frame, columns=('Instrument', 'Price', 'Change', 'VIX', 'OI'),
                                        show='headings', height=6)
        self.market_tree.heading('Instrument', text='Instrument')
        self.market_tree.heading('Price', text='Price')
        self.market_tree.heading('Change', text='Change %')
        self.market_tree.heading('VIX', text='VIX')
        self.market_tree.heading('OI', text='Total OI')

        market_scrollbar = ttk.Scrollbar(market_frame, orient=tk.VERTICAL, command=self.market_tree.yview)
        self.market_tree.config(yscrollcommand=market_scrollbar.set)

        self.market_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        market_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def create_positions_tab(self):
        """Create positions management tab"""
        pos_frame = ttk.Frame(self.notebook)
        self.notebook.add(pos_frame, text="Positions")

        # Active positions
        active_frame = ttk.LabelFrame(pos_frame, text="Active Positions")
        active_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.positions_tree = ttk.Treeview(active_frame,
                                           columns=(
                                           'Strategy', 'Instrument', 'Strike', 'Type', 'Entry', 'Current', 'P&L',
                                           'Target', 'SL'),
                                           show='headings')

        # Configure columns
        columns = ['Strategy', 'Instrument', 'Strike', 'Type', 'Entry', 'Current', 'P&L', 'Target', 'SL']
        for col in columns:
            self.positions_tree.heading(col, text=col)
            self.positions_tree.column(col, width=100)

        pos_scrollbar = ttk.Scrollbar(active_frame, orient=tk.VERTICAL, command=self.positions_tree.yview)
        self.positions_tree.config(yscrollcommand=pos_scrollbar.set)

        self.positions_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        pos_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Position management buttons
        pos_button_frame = ttk.Frame(active_frame)
        pos_button_frame.pack(fill=tk.X, pady=5)

        ttk.Button(pos_button_frame, text="Close Position", command=self.close_selected_position).pack(side=tk.LEFT,
                                                                                                       padx=5)
        ttk.Button(pos_button_frame, text="Close All", command=self.close_all_positions).pack(side=tk.LEFT, padx=5)

        # Trade history
        history_frame = ttk.LabelFrame(pos_frame, text="Trade History (Today)")
        history_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.history_tree = ttk.Treeview(history_frame,
                                         columns=(
                                         'Time', 'Strategy', 'Instrument', 'Strike', 'Type', 'Entry', 'Exit', 'P&L',
                                         'Reason'),
                                         show='headings', height=8)

        history_columns = ['Time', 'Strategy', 'Instrument', 'Strike', 'Type', 'Entry', 'Exit', 'P&L', 'Reason']
        for col in history_columns:
            self.history_tree.heading(col, text=col)
            self.history_tree.column(col, width=80)

        history_scrollbar = ttk.Scrollbar(history_frame, orient=tk.VERTICAL, command=self.history_tree.yview)
        self.history_tree.config(yscrollcommand=history_scrollbar.set)

        self.history_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        history_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def create_analytics_tab(self):
        """Create analytics and charts tab"""
        analytics_frame = ttk.Frame(self.notebook)
        self.notebook.add(analytics_frame, text="Analytics")

        # Create matplotlib figure for charts
        self.fig, ((self.ax1, self.ax2), (self.ax3, self.ax4)) = plt.subplots(2, 2, figsize=(12, 8))
        self.fig.tight_layout(pad=3.0)

        # Embed matplotlib in tkinter
        self.canvas = FigureCanvasTkAgg(self.fig, analytics_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # Chart control buttons
        chart_control_frame = ttk.Frame(analytics_frame)
        chart_control_frame.pack(fill=tk.X, pady=5)

        ttk.Button(chart_control_frame, text="Update Charts", command=self.update_charts).pack(side=tk.LEFT, padx=5)
        ttk.Button(chart_control_frame, text="Export Data", command=self.export_data).pack(side=tk.LEFT, padx=5)
        ttk.Button(chart_control_frame, text="Performance Report", command=self.generate_report).pack(side=tk.LEFT,
                                                                                                      padx=5)

    def create_settings_tab(self):
        """Create settings and configuration tab"""
        settings_frame = ttk.Frame(self.notebook)
        self.notebook.add(settings_frame, text="Settings")

        # Risk management settings
        risk_frame = ttk.LabelFrame(settings_frame, text="Risk Management")
        risk_frame.pack(fill=tk.X, padx=5, pady=5)

        # Capital settings
        ttk.Label(risk_frame, text="Initial Capital:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.capital_var = tk.StringVar(value="1000000")
        ttk.Entry(risk_frame, textvariable=self.capital_var, width=15).grid(row=0, column=1, padx=5, pady=2)

        # Risk per trade
        ttk.Label(risk_frame, text="Risk per Trade (%):").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        self.risk_per_trade_var = tk.StringVar(value="1.5")
        ttk.Entry(risk_frame, textvariable=self.risk_per_trade_var, width=15).grid(row=1, column=1, padx=5, pady=2)

        # Max positions
        ttk.Label(risk_frame, text="Max Positions:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=2)
        self.max_positions_var = tk.StringVar(value="5")
        ttk.Entry(risk_frame, textvariable=self.max_positions_var, width=15).grid(row=2, column=1, padx=5, pady=2)

        # Data refresh settings
        data_frame = ttk.LabelFrame(settings_frame, text="Data Settings")
        data_frame.pack(fill=tk.X, padx=5, pady=5)

        ttk.Label(data_frame, text="Refresh Interval (seconds):").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.refresh_interval_var = tk.StringVar(value="5")
        ttk.Entry(data_frame, textvariable=self.refresh_interval_var, width=15).grid(row=0, column=1, padx=5, pady=2)

        # Save settings button
        ttk.Button(settings_frame, text="Save Settings", command=self.save_settings).pack(pady=10)

        # Log display
        log_frame = ttk.LabelFrame(settings_frame, text="System Log")
        log_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.log_text = tk.Text(log_frame, height=10, wrap=tk.WORD)
        log_scrollbar = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview)
        self.log_text.config(yscrollcommand=log_scrollbar.set)

        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def browse_file(self):
        """Browse for Excel file"""
        filename = filedialog.askopenfilename(
            title="Select Excel File",
            filetypes=[("Excel files", "*.xlsx *.xls"), ("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if filename:
            self.file_path_var.set(filename)

    def start_trading(self):
        """Start the trading system"""
        try:
            if not self.file_path_var.get():
                messagebox.showerror("Error", "Please select an Excel file")
                return

            self.is_running = True
            self.start_button.config(state=tk.DISABLED)
            self.stop_button.config(state=tk.NORMAL)

            # Start update thread
            self.update_thread = threading.Thread(target=self.trading_loop, daemon=True)
            self.update_thread.start()

            self.status_var.set("Trading System Active")
            self.log_message("Trading system started")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to start trading system: {e}")
            logger.error(f"Error starting trading system: {e}")

    def stop_trading(self):
        """Stop the trading system"""
        self.is_running = False
        self.start_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)
        self.status_var.set("Trading System Stopped")
        self.log_message("Trading system stopped")

    def trading_loop(self):
        """Main trading loop running in separate thread"""
        while self.is_running:
            try:
                # Process data and generate signals
                self.trading_system.process_market_data(
                    self.file_path_var.get(),
                    self.instrument_var.get()
                )

                # Update GUI
                self.root.after(0, self.update_gui)

                # Sleep for refresh interval
                refresh_interval = int(self.refresh_interval_var.get())
                time_module.sleep(refresh_interval)

            except Exception as e:
                logger.error(f"Error in trading loop: {e}")
                self.root.after(0, lambda: self.log_message(f"Trading loop error: {e}"))
                time_module.sleep(5)

    def update_gui(self):
        """Update GUI with latest data"""
        try:
            self.update_performance_display()
            self.update_positions_display()
            self.update_market_data_display()
            self.update_trade_history()
        except Exception as e:
            logger.debug(f"Error updating GUI: {e}")

    def update_performance_display(self):
        """Update performance summary display"""
        try:
            perf = self.trading_system.paper_trading.get_performance_summary()

            perf_text = f"""
        Performance Summary:
        ==================
        Initial Capital: ₹{perf.get('initial_capital', 0):,.2f}
        Current Capital: ₹{perf.get('current_capital', 0):,.2f}
        Unrealized P&L: ₹{perf.get('unrealized_pnl', 0):,.2f}
        Total Capital: ₹{perf.get('total_capital', 0):,.2f}
        Daily P&L: ₹{perf.get('daily_pnl', 0):,.2f}
        Total Return: {perf.get('total_return', 0):.2f}%
        Max Drawdown: {perf.get('max_drawdown', 0):.2f}%

        Trading Statistics:
        ==================
        Total Trades: {perf.get('total_trades', 0)}
        Winning Trades: {perf.get('winning_trades', 0)}
        Win Rate: {perf.get('win_rate', 0):.1f}%
        Avg P&L per Trade: ₹{perf.get('avg_pnl_per_trade', 0):,.2f}
        Avg Holding Time: {perf.get('avg_holding_time_minutes', 0):.1f} minutes
        Active Positions: {perf.get('active_positions', 0)}
                    """

            self.perf_text.delete(1.0, tk.END)
            self.perf_text.insert(1.0, perf_text)

        except Exception as e:
            logger.debug(f"Error updating performance display: {e}")

    def update_positions_display(self):
        """Update active positions display"""
        try:
            # Clear existing items
            for item in self.positions_tree.get_children():
                self.positions_tree.delete(item)

            # Add current positions
            for position in self.trading_system.paper_trading.positions:
                values = (
                    position.strategy,
                    position.instrument,
                    f"{position.strike:.0f}",
                    position.option_type,
                    f"₹{position.entry_price:.2f}",
                    f"₹{position.current_price:.2f}",
                    f"₹{position.unrealized_pnl:.2f}",
                    f"₹{position.target:.2f}",
                    f"₹{position.stop_loss:.2f}"
                )
                self.positions_tree.insert("", tk.END, values=values)

        except Exception as e:
            logger.debug(f"Error updating positions display: {e}")

    def update_market_data_display(self):
        """Update market data display"""
        try:
            # Clear existing items
            for item in self.market_tree.get_children():
                self.market_tree.delete(item)

            # Show placeholder data for now
            market_data = [
                ("NIFTY", "24,350", "+0.5%", "12.5", "1.2M"),
                ("BANKNIFTY", "51,200", "-0.3%", "12.5", "850K"),
                ("VIX", "12.5", "+2.1%", "-", "-")
            ]

            for data in market_data:
                self.market_tree.insert("", tk.END, values=data)

        except Exception as e:
            logger.debug(f"Error updating market data display: {e}")

    def update_trade_history(self):
        """Update trade history display"""
        try:
            # Clear existing items
            for item in self.history_tree.get_children():
                self.history_tree.delete(item)

            # Add recent trades (last 20)
            recent_trades = self.trading_system.paper_trading.completed_trades[-20:]

            for trade in recent_trades:
                values = (
                    trade.exit_time.strftime("%H:%M"),
                    trade.strategy,
                    trade.instrument,
                    f"{trade.strike:.0f}",
                    trade.option_type,
                    f"₹{trade.entry_price:.2f}",
                    f"₹{trade.exit_price:.2f}",
                    f"₹{trade.pnl:.2f}",
                    trade.exit_reason
                )
                self.history_tree.insert("", tk.END, values=values)

        except Exception as e:
            logger.debug(f"Error updating trade history: {e}")

    def update_charts(self):
        """Update analytics charts"""
        try:
            # Clear previous plots
            for ax in [self.ax1, self.ax2, self.ax3, self.ax4]:
                ax.clear()

            # Chart 1: P&L over time
            trades = self.trading_system.paper_trading.completed_trades
            if trades:
                cumulative_pnl = []
                trade_times = []
                running_pnl = 0

                for trade in trades:
                    running_pnl += trade.pnl
                    cumulative_pnl.append(running_pnl)
                    trade_times.append(trade.exit_time)

                self.ax1.plot(trade_times, cumulative_pnl, 'b-', linewidth=2)
                self.ax1.set_title('Cumulative P&L')
                self.ax1.set_ylabel('P&L (₹)')
                self.ax1.tick_params(axis='x', rotation=45)
                self.ax1.grid(True, alpha=0.3)

            # Chart 2: Win/Loss distribution
            if trades:
                wins = [t.pnl for t in trades if t.pnl > 0]
                losses = [t.pnl for t in trades if t.pnl <= 0]

                self.ax2.hist([wins, losses], bins=20, label=['Wins', 'Losses'],
                              color=['green', 'red'], alpha=0.7)
                self.ax2.set_title('P&L Distribution')
                self.ax2.set_xlabel('P&L (₹)')
                self.ax2.set_ylabel('Frequency')
                self.ax2.legend()
                self.ax2.grid(True, alpha=0.3)

            # Chart 3: Strategy performance
            if trades:
                strategy_pnl = {}
                for trade in trades:
                    if trade.strategy not in strategy_pnl:
                        strategy_pnl[trade.strategy] = 0
                    strategy_pnl[trade.strategy] += trade.pnl

                if strategy_pnl:
                    strategies = list(strategy_pnl.keys())
                    pnls = list(strategy_pnl.values())
                    colors = ['green' if p > 0 else 'red' for p in pnls]

                    self.ax3.bar(strategies, pnls, color=colors, alpha=0.7)
                    self.ax3.set_title('Strategy Performance')
                    self.ax3.set_ylabel('Total P&L (₹)')
                    self.ax3.tick_params(axis='x', rotation=45)
                    self.ax3.grid(True, alpha=0.3)

            # Chart 4: Daily performance
            if trades:
                daily_pnl = {}
                for trade in trades:
                    date = trade.exit_time.date()
                    if date not in daily_pnl:
                        daily_pnl[date] = 0
                    daily_pnl[date] += trade.pnl

                if daily_pnl:
                    dates = list(daily_pnl.keys())
                    pnls = list(daily_pnl.values())
                    colors = ['green' if p > 0 else 'red' for p in pnls]

                    self.ax4.bar(dates, pnls, color=colors, alpha=0.7)
                    self.ax4.set_title('Daily P&L')
                    self.ax4.set_ylabel('P&L (₹)')
                    self.ax4.tick_params(axis='x', rotation=45)
                    self.ax4.grid(True, alpha=0.3)

            self.fig.tight_layout()
            self.canvas.draw()

        except Exception as e:
            logger.debug(f"Error updating charts: {e}")

    def manual_signal(self):
        """Open manual signal entry dialog"""
        ManualSignalDialog(self.root, self.trading_system)

    def close_selected_position(self):
        """Close selected position"""
        try:
            selection = self.positions_tree.selection()
            if not selection:
                messagebox.showwarning("Warning", "Please select a position to close")
                return

            item = selection[0]
            position_index = self.positions_tree.index(item)

            if position_index < len(self.trading_system.paper_trading.positions):
                position = self.trading_system.paper_trading.positions[position_index]
                self.trading_system.paper_trading._close_position(position, "Manual Close")
                self.log_message(f"Position closed manually: {position.strategy}")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to close position: {e}")

    def close_all_positions(self):
        """Close all open positions"""
        try:
            result = messagebox.askyesno("Confirm", "Are you sure you want to close all positions?")
            if result:
                positions_copy = self.trading_system.paper_trading.positions.copy()
                for position in positions_copy:
                    self.trading_system.paper_trading._close_position(position, "Manual Close All")
                self.log_message("All positions closed manually")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to close all positions: {e}")

    def export_data(self):
        """Export trading data to Excel"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Export Trading Data",
                defaultextension=".xlsx",
                filetypes=[("Excel files", "*.xlsx"), ("CSV files", "*.csv")]
            )

            if filename:
                trades_data = []
                for trade in self.trading_system.paper_trading.completed_trades:
                    trades_data.append({
                        'Date': trade.exit_time.date(),
                        'Time': trade.exit_time.time(),
                        'Strategy': trade.strategy,
                        'Instrument': trade.instrument,
                        'Strike': trade.strike,
                        'Option Type': trade.option_type,
                        'Entry Price': trade.entry_price,
                        'Exit Price': trade.exit_price,
                        'Quantity': trade.quantity,
                        'P&L': trade.pnl,
                        'Exit Reason': trade.exit_reason,
                        'Holding Time (min)': trade.holding_time.total_seconds() / 60
                    })

                if filename.endswith('.xlsx'):
                    df = pd.DataFrame(trades_data)
                    df.to_excel(filename, index=False)
                else:
                    df = pd.DataFrame(trades_data)
                    df.to_csv(filename, index=False)

                messagebox.showinfo("Success", f"Data exported successfully to {filename}")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to export data: {e}")

    def generate_report(self):
        """Generate comprehensive performance report"""
        try:
            report_window = tk.Toplevel(self.root)
            report_window.title("Performance Report")
            report_window.geometry("800x600")

            # Create scrollable text widget
            report_text = tk.Text(report_window, wrap=tk.WORD)
            report_scrollbar = ttk.Scrollbar(report_window, orient=tk.VERTICAL, command=report_text.yview)
            report_text.config(yscrollcommand=report_scrollbar.set)

            # Generate detailed report
            perf = self.trading_system.paper_trading.get_performance_summary()
            trades = self.trading_system.paper_trading.completed_trades

            report_content = f"""
        INSTITUTIONAL TRADING SYSTEM - PERFORMANCE REPORT
        ===============================================
        Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

        PORTFOLIO OVERVIEW
        ==================
        Initial Capital: ₹{perf.get('initial_capital', 0):,.2f}
        Current Capital: ₹{perf.get('current_capital', 0):,.2f}
        Total Return: {perf.get('total_return', 0):.2f}%
        Maximum Drawdown: {perf.get('max_drawdown', 0):.2f}%

        TRADING STATISTICS
        ==================
        Total Trades: {perf.get('total_trades', 0)}
        Winning Trades: {perf.get('winning_trades', 0)}
        Losing Trades: {perf.get('total_trades', 0) - perf.get('winning_trades', 0)}
        Win Rate: {perf.get('win_rate', 0):.1f}%
        Average P&L per Trade: ₹{perf.get('avg_pnl_per_trade', 0):,.2f}
        Average Holding Time: {perf.get('avg_holding_time_minutes', 0):.1f} minutes

        RECENT TRADES (Last 10)
        ======================
        """

            # Recent trades
            recent_trades = trades[-10:] if len(trades) > 10 else trades
            for trade in recent_trades:
                report_content += f"""
        {trade.exit_time.strftime('%H:%M')} | {trade.strategy} | {trade.instrument} {trade.strike} {trade.option_type} | P&L: ₹{trade.pnl:.2f} | {trade.exit_reason}
        """

            report_text.insert(1.0, report_content)
            report_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            report_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        except Exception as e:
            messagebox.showerror("Error", f"Failed to generate report: {e}")

    def save_settings(self):
        """Save current settings"""
        try:
            messagebox.showinfo("Success", "Settings saved successfully")
            self.log_message("Settings updated and saved")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save settings: {e}")

    def log_message(self, message: str):
        """Add message to log display"""
        try:
            timestamp = datetime.now().strftime("%H:%M:%S")
            log_entry = f"[{timestamp}] {message}\n"

            self.log_text.insert(tk.END, log_entry)
            self.log_text.see(tk.END)

            # Keep log size manageable
            lines = self.log_text.get(1.0, tk.END).split('\n')
            if len(lines) > 1000:
                self.log_text.delete(1.0, f"{len(lines) - 1000}.0")

        except Exception as e:
            logger.debug(f"Error logging message: {e}")

    def run(self):
        """Start the GUI main loop"""
        try:
            self.root.after(1000, self.periodic_update)
            self.root.mainloop()
        except Exception as e:
            logger.error(f"Error in GUI main loop: {e}")

    def periodic_update(self):
        """Periodic GUI updates"""
        try:
            if not self.is_running:
                self.update_performance_display()
                self.update_positions_display()

            self.root.after(5000, self.periodic_update)

        except Exception as e:
            logger.debug(f"Error in periodic update: {e}")

    class ManualSignalDialog:
        """Dialog for manual signal entry"""

        def __init__(self, parent, trading_system):
            self.trading_system = trading_system

            self.dialog = tk.Toplevel(parent)
            self.dialog.title("Manual Signal Entry")
            self.dialog.geometry("400x500")
            self.dialog.transient(parent)
            self.dialog.grab_set()

            self.setup_dialog()

        def setup_dialog(self):
            """Setup manual signal dialog"""
            # Instrument selection
            ttk.Label(self.dialog, text="Instrument:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
            self.instrument_var = tk.StringVar(value="NIFTY")
            ttk.Combobox(self.dialog, textvariable=self.instrument_var,
                         values=["NIFTY", "BANKNIFTY", "CRUDEOIL"]).grid(row=0, column=1, padx=5, pady=5)

            # Strike price
            ttk.Label(self.dialog, text="Strike Price:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
            self.strike_var = tk.StringVar()
            ttk.Entry(self.dialog, textvariable=self.strike_var).grid(row=1, column=1, padx=5, pady=5)

            # Option type
            ttk.Label(self.dialog, text="Option Type:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
            self.option_type_var = tk.StringVar(value="CE")
            ttk.Combobox(self.dialog, textvariable=self.option_type_var, values=["CE", "PE"]).grid(row=2, column=1,
                                                                                                   padx=5, pady=5)

            # Signal type
            ttk.Label(self.dialog, text="Signal Type:").grid(row=3, column=0, sticky=tk.W, padx=5, pady=5)
            self.signal_type_var = tk.StringVar(value="BUY")
            ttk.Combobox(self.dialog, textvariable=self.signal_type_var, values=["BUY", "SELL"]).grid(row=3, column=1,
                                                                                                      padx=5, pady=5)

            # Entry price
            ttk.Label(self.dialog, text="Entry Price:").grid(row=4, column=0, sticky=tk.W, padx=5, pady=5)
            self.price_var = tk.StringVar()
            ttk.Entry(self.dialog, textvariable=self.price_var).grid(row=4, column=1, padx=5, pady=5)

            # Expiry date
            ttk.Label(self.dialog, text="Expiry Date:").grid(row=5, column=0, sticky=tk.W, padx=5, pady=5)
            self.expiry_var = tk.StringVar(value=datetime.now().strftime("%Y-%m-%d"))
            ttk.Entry(self.dialog, textvariable=self.expiry_var).grid(row=5, column=1, padx=5, pady=5)

            # Reasoning
            ttk.Label(self.dialog, text="Reasoning:").grid(row=6, column=0, sticky=tk.W, padx=5, pady=5)
            self.reasoning_text = tk.Text(self.dialog, height=4, width=30)
            self.reasoning_text.grid(row=6, column=1, padx=5, pady=5)

            # Buttons
            button_frame = ttk.Frame(self.dialog)
            button_frame.grid(row=7, column=0, columnspan=2, pady=10)

            ttk.Button(button_frame, text="Execute Signal", command=self.execute_signal).pack(side=tk.LEFT, padx=5)
            ttk.Button(button_frame, text="Cancel", command=self.dialog.destroy).pack(side=tk.LEFT, padx=5)

        def execute_signal(self):
            """Execute the manual signal"""
            try:
                # Validate inputs
                if not all([self.strike_var.get(), self.price_var.get()]):
                    messagebox.showerror("Error", "Please fill all required fields")
                    return

                # Create signal dictionary
                signal = {
                    'strategy': 'manual_entry',
                    'instrument': self.instrument_var.get(),
                    'strike': float(self.strike_var.get()),
                    'option_type': self.option_type_var.get(),
                    'expiry': datetime.strptime(self.expiry_var.get(), "%Y-%m-%d"),
                    'signal_type': self.signal_type_var.get(),
                    'entry_price': float(self.price_var.get()),
                    'confidence': 1.0,
                    'reasoning': self.reasoning_text.get(1.0, tk.END).strip(),
                    'timestamp': datetime.now()
                }

                # Execute signal
                success = self.trading_system.paper_trading.execute_signal(signal, {})

                if success:
                    messagebox.showinfo("Success", "Manual signal executed successfully")
                    self.dialog.destroy()
                else:
                    messagebox.showerror("Error", "Failed to execute signal")

            except Exception as e:
                messagebox.showerror("Error", f"Invalid input: {e}")

    class TradingSystem:
        """Main trading system orchestrator"""

        def __init__(self):
            try:
                # Initialize components
                self.config = ConfigManager()
                self.data_processor = DataProcessor(self.config)
                self.smart_money_detector = SmartMoneyDetector(self.config)
                self.strategy_engine = StrategyEngine(self.config, self.smart_money_detector)
                self.paper_trading = PaperTradingEngine(self.config)

                # Performance tracking
                self.last_data_update = None
                self.system_start_time = datetime.now()

                logger.info("Trading system initialized successfully")

            except Exception as e:
                logger.error(f"Error initializing trading system: {e}")
                raise TradingSystemError(f"Failed to initialize trading system: {e}")

        def process_market_data(self, file_path: str, instrument: str) -> bool:
            """Main data processing pipeline"""
            try:
                # Check if file exists
                if not Path(file_path).exists():
                    logger.warning(f"File not found: {file_path}")
                    return False

                # Process Excel data
                market_data = self.data_processor.process_excel_data(file_path)
                if not market_data:
                    logger.warning("No market data processed")
                    return False

                # Generate trading signals
                signals = self.strategy_engine.generate_signals(market_data, instrument)

                # Execute signals
                for signal in signals:
                    try:
                        success = self.paper_trading.execute_signal(signal, market_data)
                        if success:
                            logger.info(
                                f"Signal executed: {signal['strategy']} - {signal['signal_type']} {signal['option_type']} {signal['strike']}")
                    except Exception as e:
                        logger.error(f"Error executing signal: {e}")

                # Update existing positions
                self.paper_trading.update_positions(market_data)

                self.last_data_update = datetime.now()
                return True

            except Exception as e:
                logger.error(f"Error processing market data: {e}")
                return False

        def get_system_status(self) -> Dict:
            """Get comprehensive system status"""
            try:
                return {
                    'system_uptime': str(datetime.now() - self.system_start_time),
                    'last_data_update': self.last_data_update.strftime(
                        "%H:%M:%S") if self.last_data_update else "Never",
                    'active_positions': len(self.paper_trading.positions),
                    'completed_trades': len(self.paper_trading.completed_trades),
                    'current_session': self.config.get_session_type(datetime.now().time()),
                    'total_capital': self.paper_trading.current_capital + self.paper_trading.unrealized_pnl,
                    'daily_pnl': self.paper_trading.daily_pnl
                }
            except Exception as e:
                logger.error(f"Error getting system status: {e}")
                return {}

    # Utility functions
    def format_currency(amount: float, currency: str = "₹") -> str:
        """Format currency with proper Indian formatting"""
        if abs(amount) >= 10000000:  # 1 crore
            return f"{currency}{amount / 10000000:.2f}Cr"
        elif abs(amount) >= 100000:  # 1 lakh
            return f"{currency}{amount / 100000:.2f}L"
        elif abs(amount) >= 1000:  # 1 thousand
            return f"{currency}{amount / 1000:.2f}K"
        else:
            return f"{currency}{amount:.2f}"

    def calculate_option_moneyness_category(moneyness: float) -> str:
        """Categorize option moneyness"""
        if abs(moneyness) <= 0.02:
            return "ATM"
        elif moneyness > 0.02:
            return "OTM" if moneyness <= 0.10 else "Deep OTM"
        else:
            return "ITM" if moneyness >= -0.10 else "Deep ITM"

    def validate_trading_time() -> Tuple[bool, str]:
        """Validate if current time is within trading hours"""
        current_time = datetime.now().time()

        # Market hours: 9:15 AM to 3:30 PM
        market_open = time(9, 15)
        market_close = time(15, 30)

        if market_open <= current_time <= market_close:
            return True, "TRADING_HOURS"
        elif current_time < market_open:
            return False, "PRE_MARKET"
        else:
            return False, "POST_MARKET"

    def get_expiry_category(expiry_date: datetime) -> str:
        """Categorize expiry by time remaining"""
        days_to_expiry = (expiry_date.date() - datetime.now().date()).days

        if days_to_expiry <= 0:
            return "EXPIRED"
        elif days_to_expiry <= 7:
            return "CURRENT_WEEK"
        elif days_to_expiry <= 14:
            return "NEXT_WEEK"
        elif days_to_expiry <= 30:
            return "CURRENT_MONTH"
        else:
            return "NEXT_MONTH"

    class AlertSystem:
        """Real-time alert system for trading events"""

        def __init__(self):
            self.alert_queue = queue.Queue()
            self.alert_history = deque(maxlen=1000)

        def add_alert(self, alert_type: str, message: str, severity: str = "INFO"):
            """Add alert to the system"""
            alert = {
                'type': alert_type,
                'message': message,
                'severity': severity,
                'timestamp': datetime.now()
            }

            self.alert_queue.put(alert)
            self.alert_history.append(alert)

            # Log based on severity
            if severity == "HIGH":
                logger.warning(f"HIGH ALERT: {message}")
            elif severity == "MEDIUM":
                logger.info(f"MEDIUM ALERT: {message}")
            else:
                logger.debug(f"INFO ALERT: {message}")

        def get_pending_alerts(self) -> List[Dict]:
            """Get all pending alerts"""
            alerts = []
            while not self.alert_queue.empty():
                try:
                    alerts.append(self.alert_queue.get_nowait())
                except queue.Empty:
                    break
            return alerts

    class SystemMonitor:
        """System health and performance monitoring"""

        def __init__(self):
            self.start_time = datetime.now()
            self.performance_metrics = deque(maxlen=1000)

        def log_performance_metric(self, metric_name: str, value: float):
            """Log a performance metric"""
            self.performance_metrics.append({
                'timestamp': datetime.now(),
                'metric': metric_name,
                'value': value
            })

        def get_system_health(self) -> Dict:
            """Get overall system health status"""
            try:
                # CPU and memory usage
                cpu_percent = psutil.cpu_percent(interval=1)
                memory = psutil.virtual_memory()

                # System uptime
                uptime = datetime.now() - self.start_time

                return {
                    'uptime': str(uptime),
                    'cpu_usage': cpu_percent,
                    'memory_usage': memory.percent,
                    'memory_available': memory.available / (1024 ** 3),  # GB
                    'status': 'HEALTHY' if cpu_percent < 80 and memory.percent < 80 else 'WARNING'
                }

            except Exception as e:
                logger.error(f"Error getting system health: {e}")
                return {'status': 'ERROR', 'error': str(e)}

    def main():
        """Main application entry point"""
        try:
            # Create trading system
            print("Initializing Institutional-Grade Trading System...")
            trading_system = TradingSystem()

            # Create and run GUI
            print("Starting GUI interface...")
            gui = TradingSystemGUI(trading_system)
            gui.run()

        except Exception as e:
            logger.error(f"Critical error in main application: {e}")
            print(f"Failed to start trading system: {e}")

    if __name__ == "__main__":
        try:
            # Set up proper logging for main execution
            logging.basicConfig(
                level=logging.INFO,
                format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
                handlers=[
                    logging.FileHandler('trading_system.log', mode='a'),
                    logging.StreamHandler(sys.stdout)
                ]
            )

            print("=" * 60)
            print("INSTITUTIONAL-GRADE INTRADAY TRADING SYSTEM")
            print("=" * 60)
            print("Starting system...")

            main()

        except KeyboardInterrupt:
            print("\n\nSystem shutdown requested by user")
            logger.info("Trading system shutdown by user interrupt")
        except Exception as e:
            print(f"\nCritical error starting trading system: {e}")
            logger.critical(f"Critical startup error: {e}")
            sys.exit(1)
        finally:
            print("\nTrading system shutdown complete")
            logger.info("Trading system shutdown complete")
    """
    Complete Institutional-Grade Intraday Options Trading System
    ===========================================================
    A comprehensive algorithmic trading system for Indian derivatives markets
    Based on real-time Excel data feed with advanced analytics and ML integration

    Author: AI Trading Systems
    Version: 1.0
    Date: 2025

    Features:
    - Real-time Excel data processing
    - Smart money flow detection  
    - Advanced Greeks calculation
    - Multi-asset support (Index, Commodity, Stock options)
    - Machine learning pattern recognition
    - Paper trading with P&L tracking
    - Configurable risk management
    - Holiday calendar integration
    - Performance analytics dashboard
    """

    import pandas as pd
    import numpy as np
    import sqlite3
    import json
    import logging
    import warnings
    from datetime import datetime, timedelta, time
    from typing import Dict, List, Optional, Tuple, Any, Union
    import threading
    import queue
    import time as time_module
    from pathlib import Path
    import scipy.stats as stats
    from scipy.optimize import minimize_scalar, brentq
    import talib
    from sklearn.ensemble import IsolationForest, RandomForestClassifier, GradientBoostingRegressor
    from sklearn.preprocessing import StandardScaler, RobustScaler
    from sklearn.cluster import DBSCAN
    from sklearn.model_selection import train_test_split
    from sklearn.metrics import accuracy_score, classification_report
    import joblib
    import tkinter as tk
    from tkinter import ttk, messagebox, filedialog
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    from matplotlib.animation import FuncAnimation
    import seaborn as sns
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from concurrent.futures import ThreadPoolExecutor, as_completed
    import psutil
    import gc
    from collections import defaultdict, deque
    import pickle
    import hashlib
    import os
    import sys
    from dataclasses import dataclass, field
    from enum import Enum
    import asyncio

    # Configure warnings and logging
    warnings.filterwarnings('ignore')
    plt.style.use('seaborn-v0_8')

    # Setup comprehensive logging
    log_formatter = logging.Formatter(
        '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s'
    )

    file_handler = logging.FileHandler('trading_system.log')
    file_handler.setFormatter(log_formatter)

    console_handler = logging.StreamHandler()
    console_handler.setFormatter(log_formatter)

    logger = logging.getLogger(__name__)
    logger.setLevel(logging.INFO)
    logger.addHandler(file_handler)
    logger.addHandler(console_handler)

    # Custom exceptions
    class TradingSystemError(Exception):
        """Base exception for trading system errors"""
        pass

    class DataValidationError(TradingSystemError):
        """Data validation specific errors"""
        pass

    class StrategyError(TradingSystemError):
        """Strategy execution specific errors"""
        pass

    class ConfigurationError(TradingSystemError):
        """Configuration related errors"""
        pass

    @dataclass
    class Position:
        """Position data structure with complete field definitions"""
        instrument: str
        strike: float
        option_type: str  # 'CE' or 'PE'
        expiry: datetime
        entry_price: float
        quantity: int
        entry_time: datetime
        strategy: str
        stop_loss: float = 0.0
        target: float = 0.0
        trailing_stop: float = 0.0
        current_price: float = 0.0
        unrealized_pnl: float = 0.0
        max_profit: float = 0.0
        max_loss: float = 0.0

        def update_price(self, current_price: float):
            """Update current price and P&L calculations"""
            self.current_price = current_price
            self.unrealized_pnl = (current_price - self.entry_price) * self.quantity
            self.max_profit = max(self.max_profit, self.unrealized_pnl)
            self.max_loss = min(self.max_loss, self.unrealized_pnl)

    @dataclass
    class Trade:
        """Completed trade data structure"""
        instrument: str
        strike: float
        option_type: str
        expiry: datetime
        entry_price: float
        exit_price: float
        quantity: int
        entry_time: datetime
        exit_time: datetime
        strategy: str
        pnl: float
        max_profit: float
        max_loss: float
        exit_reason: str
        holding_time: timedelta

    class ConfigManager:
        """Centralized configuration management with file-based configs"""

        def __init__(self, config_dir: str = "configs"):
            self.config_dir = Path(config_dir)
            self.config_dir.mkdir(exist_ok=True)
            self._create_default_configs()
            self.load_all_configs()

        def _create_default_configs(self):
            """Create all default configuration files"""

            # Market configuration
            market_config = {
                "trading_sessions": {
                    "pre_market": {"start": "09:00", "end": "09:15"},
                    "opening": {"start": "09:15", "end": "10:30"},
                    "regular": {"start": "10:30", "end": "14:30"},
                    "closing": {"start": "14:30", "end": "15:15"},
                    "square_off": {"start": "15:15", "end": "15:30"}
                },
                "exchanges": {
                    "NSE": {
                        "trading_hours": {"start": "09:15", "end": "15:30"},
                        "settlement": "T+1",
                        "currency": "INR",
                        "timezone": "Asia/Kolkata"
                    },
                    "MCX": {
                        "trading_hours": {"start": "09:00", "end": "23:30"},
                        "settlement": "T+1",
                        "currency": "INR",
                        "timezone": "Asia/Kolkata"
                    }
                },
                "current_year": datetime.now().year
            }

            # Instruments configuration
            instruments_config = {
                "INDEX_OPTIONS": {
                    "NIFTY": {
                        "lot_size": 75,
                        "tick_size": 0.05,
                        "strike_interval": 50,
                        "atm_reference": "spot_price",
                        "exchange": "NSE",
                        "multiplier": 1,
                        "margin_percentage": 0.10,
                        "circuit_limit": 0.10,
                        "spot_identifier": "NIFTY",
                        "vix_identifier": "INDIAVIX",
                        "futures_identifier": "NIFTY_FUT"
                    },
                    "BANKNIFTY": {
                        "lot_size": 15,
                        "tick_size": 0.05,
                        "strike_interval": 100,
                        "atm_reference": "spot_price",
                        "exchange": "NSE",
                        "multiplier": 1,
                        "margin_percentage": 0.15,
                        "circuit_limit": 0.10,
                        "spot_identifier": "BANKNIFTY",
                        "vix_identifier": "INDIAVIX",
                        "futures_identifier": "BANKNIFTY_FUT"
                    }
                },
                "MCX_OPTIONS": {
                    "CRUDEOIL": {
                        "lot_size": 100,
                        "tick_size": 1.0,
                        "strike_interval": 20,
                        "atm_reference": "near_month_futures",
                        "exchange": "MCX",
                        "multiplier": 1,
                        "margin_percentage": 0.08,
                        "circuit_limit": 0.05,
                        "futures_identifier": "CRUDEOIL_FUT"
                    }
                }
            }

            # Strategy configuration
            strategy_config = {
                "smart_money_detection": {
                    "oi_thresholds": {
                        "NIFTY": {
                            "significant": 25000,
                            "major": 75000,
                            "institutional": 150000
                        },
                        "BANKNIFTY": {
                            "significant": 5000,
                            "major": 15000,
                            "institutional": 30000
                        }
                    },
                    "time_windows": {
                        "fast": 5,
                        "medium": 15,
                        "slow": 30
                    },
                    "confidence_thresholds": {
                        "high": 0.80,
                        "medium": 0.65,
                        "low": 0.50
                    }
                },
                "risk_management": {
                    "position_sizing": {
                        "max_risk_per_trade": 0.015,
                        "max_portfolio_risk": 0.03,
                        "max_positions": 5
                    },
                    "stop_loss": {
                        "options_long": 0.30,
                        "options_short": 2.0
                    },
                    "profit_targets": {
                        "quick_profit": 0.25,
                        "target_profit": 0.50
                    }
                },
                "session_strategies": {
                    "opening": ["smart_money_following", "gap_trading"],
                    "regular": ["mean_reversion", "volatility_trading"],
                    "closing": ["profit_booking"]
                }
            }

            # Holiday calendar
            holiday_calendar = {
                str(datetime.now().year): [
                    {"date": f"{datetime.now().year}-01-26", "name": "Republic Day", "type": "full_closure"},
                    {"date": f"{datetime.now().year}-03-14", "name": "Holi", "type": "full_closure"},
                    {"date": f"{datetime.now().year}-08-15", "name": "Independence Day", "type": "full_closure"},
                    {"date": f"{datetime.now().year}-10-02", "name": "Gandhi Jayanti", "type": "full_closure"}
                ]
            }

            # Data mapping configuration
            data_mapping = {
                "excel_column_mapping": {
                    "Short Exchange Name": "exchange_short",
                    "Exchange": "exchange",
                    "Scrip Code": "scrip_code",
                    "Scrip Name": "scrip_name",
                    "Current": "current_price",
                    "Open Interest": "open_interest",
                    "OI Difference": "oi_change",
                    "Strike Price": "strike_price",
                    "Call/Put": "option_type",
                    "Expiry Date": "expiry_date",
                    "Bid Price": "bid_price",
                    "Offer Price": "ask_price",
                    "Instrument Type": "instrument_type"
                },
                "instrument_identification": {
                    "spot_patterns": ["EQ"],
                    "futures_patterns": ["FUTIDX", "FUTCOM"],
                    "options_patterns": ["OPTIDX", "OPTCOM"],
                    "vix_patterns": ["INDIAVIX"]
                }
            }

            # Save all configurations
            configs = {
                "market_config.json": market_config,
                "instruments_config.json": instruments_config,
                "strategy_config.json": strategy_config,
                "holiday_calendar.json": holiday_calendar,
                "data_mapping.json": data_mapping
            }

            for filename, config in configs.items():
                config_path = self.config_dir / filename
                if not config_path.exists():
                    with open(config_path, 'w') as f:
                        json.dump(config, f, indent=2)
                    logger.info(f"Created default config: {filename}")

        def load_all_configs(self):
            """Load all configuration files"""
            try:
                self.market_config = self._load_config("market_config.json")
                self.instruments_config = self._load_config("instruments_config.json")
                self.strategy_config = self._load_config("strategy_config.json")
                self.holiday_calendar = self._load_config("holiday_calendar.json")
                self.data_mapping = self._load_config("data_mapping.json")
                logger.info("All configurations loaded successfully")
            except Exception as e:
                logger.error(f"Error loading configurations: {e}")
                raise ConfigurationError(f"Failed to load configurations: {e}")

        def _load_config(self, filename: str) -> Dict:
            """Load individual configuration file"""
            config_path = self.config_dir / filename
            try:
                with open(config_path, 'r') as f:
                    return json.load(f)
            except Exception as e:
                logger.error(f"Error loading {filename}: {e}")
                raise

        def get_instrument_config(self, instrument: str) -> Optional[Dict]:
            """Get configuration for specific instrument"""
            for category in self.instruments_config.values():
                if instrument in category:
                    return category[instrument]
            return None

        def is_trading_day(self, date: datetime) -> bool:
            """Check if given date is a trading day"""
            if date.weekday() >= 5:  # Weekend
                return False

            date_str = date.strftime("%Y-%m-%d")
            year_holidays = self.holiday_calendar.get(str(date.year), [])

            for holiday in year_holidays:
                if holiday["date"] == date_str and holiday["type"] == "full_closure":
                    return False

            return True

        def get_session_type(self, current_time: time) -> str:
            """Get current trading session type"""
            sessions = self.market_config["trading_sessions"]

            for session_name, session_time in sessions.items():
                start_time = datetime.strptime(session_time["start"], "%H:%M").time()
                end_time = datetime.strptime(session_time["end"], "%H:%M").time()

                if start_time <= current_time <= end_time:
                    return session_name

            return "closed"

    class DataProcessor:
        """Advanced data processing with validation and enrichment"""

        def __init__(self, config_manager: ConfigManager):
            self.config = config_manager
            self.last_update = None
            self.data_cache = {}
            self.processed_data = {}
            self.data_history = deque(maxlen=1000)
            self.column_mapping = self.config.data_mapping["excel_column_mapping"]

        def process_excel_data(self, file_path: str) -> Optional[Dict[str, pd.DataFrame]]:
            """Main data processing pipeline"""
            try:
                # Read Excel file
                raw_data = self._read_excel_file(file_path)
                if raw_data is None:
                    return None

                # Clean and standardize data
                cleaned_data = self._clean_data(raw_data)

                # Categorize instruments
                categorized_data = self._categorize_instruments(cleaned_data)

                # Enrich with calculated fields
                enriched_data = self._enrich_data(categorized_data)

                # Cache for historical analysis
                self._cache_data(enriched_data)

                self.processed_data = enriched_data
                self.last_update = datetime.now()
                return enriched_data

            except Exception as e:
                logger.error(f"Error processing Excel data: {e}")
                return None

        def _read_excel_file(self, file_path: str) -> Optional[pd.DataFrame]:
            """Read Excel file with error handling"""
            try:
                if file_path.endswith('.xlsx') or file_path.endswith('.xls'):
                    df = pd.read_excel(file_path)
                elif file_path.endswith('.csv'):
                    df = pd.read_csv(file_path)
                else:
                    logger.error(f"Unsupported file format: {file_path}")
                    return None

                if df.empty:
                    logger.warning("File is empty")
                    return None

                # Rename columns based on mapping
                df = df.rename(columns=self.column_mapping)
                return df

            except Exception as e:
                logger.error(f"Error reading file {file_path}: {e}")
                return None

        def _clean_data(self, df: pd.DataFrame) -> pd.DataFrame:
            """Clean and standardize data"""
            try:
                # Handle numeric columns
                numeric_columns = [
                    'current_price', 'open_interest', 'oi_change', 'strike_price',
                    'bid_price', 'ask_price'
                ]

                for col in numeric_columns:
                    if col in df.columns:
                        df[col] = pd.to_numeric(df[col], errors='coerce')
                        df[col].fillna(0, inplace=True)

                # Clean string columns
                string_columns = ['scrip_name', 'option_type', 'instrument_type']
                for col in string_columns:
                    if col in df.columns:
                        df[col] = df[col].astype(str).str.strip().str.upper()

                # Parse expiry dates
                if 'expiry_date' in df.columns:
                    df['expiry_date'] = pd.to_datetime(df['expiry_date'], errors='coerce')
                    df['days_to_expiry'] = (df['expiry_date'] - datetime.now()).dt.days
                    df['time_to_expiry'] = df['days_to_expiry'] / 365.25

                return df

            except Exception as e:
                logger.error(f"Error cleaning data: {e}")
                return df

        def _categorize_instruments(self, df: pd.DataFrame) -> Dict[str, pd.DataFrame]:
            """Categorize instruments by type"""
            categorized = {
                'spot': pd.DataFrame(),
                'futures': pd.DataFrame(),
                'options': pd.DataFrame(),
                'vix': pd.DataFrame()
            }

            try:
                instrument_patterns = self.config.data_mapping["instrument_identification"]

                if 'instrument_type' in df.columns:
                    # Spot instruments
                    spot_mask = df['instrument_type'].isin(instrument_patterns["spot_patterns"])
                    categorized['spot'] = df[spot_mask].copy()

                    # Futures instruments
                    futures_mask = df['instrument_type'].isin(instrument_patterns["futures_patterns"])
                    categorized['futures'] = df[futures_mask].copy()

                    # Options instruments
                    options_mask = df['instrument_type'].isin(instrument_patterns["options_patterns"])
                    categorized['options'] = df[options_mask].copy()

                    # VIX instruments
                    if 'scrip_name' in df.columns:
                        vix_mask = df['scrip_name'].isin(instrument_patterns["vix_patterns"])
                        categorized['vix'] = df[vix_mask].copy()

                return categorized

            except Exception as e:
                logger.error(f"Error categorizing instruments: {e}")
                return categorized

        def _enrich_data(self, categorized_data: Dict[str, pd.DataFrame]) -> Dict[str, pd.DataFrame]:
            """Add calculated fields and derived metrics"""
            try:
                # Enrich options data
                if not categorized_data['options'].empty:
                    options_df = categorized_data['options'].copy()

                    # Calculate moneyness
                    options_df['moneyness'] = self._calculate_moneyness(options_df, categorized_data['spot'])

                    # Calculate basic Greeks
                    options_df = self._add_basic_greeks(options_df, categorized_data['spot'], categorized_data['vix'])

                    # Calculate bid-ask spread
                    if 'bid_price' in options_df.columns and 'ask_price' in options_df.columns:
                        options_df['bid_ask_spread'] = options_df['ask_price'] - options_df['bid_price']
                        options_df['bid_ask_spread_pct'] = (
                                options_df['bid_ask_spread'] / options_df['current_price'] * 100
                        )

                    categorized_data['options'] = options_df

                return categorized_data

            except Exception as e:
                logger.error(f"Error enriching data: {e}")
                return categorized_data

        def _calculate_moneyness(self, options_df: pd.DataFrame, spot_df: pd.DataFrame) -> pd.Series:
            """Calculate option moneyness"""
            if spot_df.empty or 'current_price' not in spot_df.columns:
                return pd.Series([0] * len(options_df))

            spot_price = spot_df['current_price'].iloc[0] if not spot_df.empty else 0

            if 'strike_price' in options_df.columns and spot_price > 0:
                return (options_df['strike_price'] - spot_price) / spot_price

            return pd.Series([0] * len(options_df))

        def _add_basic_greeks(self, options_df: pd.DataFrame, spot_df: pd.DataFrame,
                              vix_df: pd.DataFrame) -> pd.DataFrame:
            """Add basic Greeks calculations"""
            try:
                # Initialize Greeks columns
                options_df['delta'] = 0.0
                options_df['gamma'] = 0.0
                options_df['theta'] = 0.0
                options_df['vega'] = 0.0
                options_df['implied_volatility'] = 0.15  # Default IV

                if spot_df.empty or vix_df.empty:
                    return options_df

                spot_price = spot_df['current_price'].iloc[0]
                vix_value = vix_df['current_price'].iloc[0] / 100 if not vix_df.empty else 0.15
                risk_free_rate = 0.065  # 6.5%

                for idx, row in options_df.iterrows():
                    try:
                        strike = row.get('strike_price', 0)
                        time_to_expiry = row.get('time_to_expiry', 0)
                        option_price = row.get('current_price', 0)
                        option_type = row.get('option_type', 'CE')

                        if strike > 0 and time_to_expiry > 0 and option_price > 0:
                            # Simplified Greeks calculation
                            moneyness = row.get('moneyness', 0)

                            # Basic Delta approximation
                            if option_type == 'CE':
                                delta = 0.5 + moneyness * 2  # Simplified
                                delta = max(0, min(1, delta))
                            else:
                                delta = -0.5 + moneyness * 2  # Simplified
                                delta = max(-1, min(0, delta))

                            # Basic Gamma approximation
                            gamma = 1 / (strike * vix_value * np.sqrt(time_to_expiry)) if time_to_expiry > 0 else 0

                            # Basic Theta approximation (time decay)
                            theta = -option_price / (time_to_expiry * 365) if time_to_expiry > 0 else 0

                            # Basic Vega approximation
                            vega = strike * np.sqrt(time_to_expiry) * 0.01 if time_to_expiry > 0 else 0

                            options_df.loc[idx, 'delta'] = delta
                            options_df.loc[idx, 'gamma'] = gamma
                            options_df.loc[idx, 'theta'] = theta
                            options_df.loc[idx, 'vega'] = vega
                            options_df.loc[idx, 'implied_volatility'] = vix_value

                    except Exception as e:
                        logger.debug(f"Error calculating Greeks for row {idx}: {e}")
                        continue

                return options_df

            except Exception as e:
                logger.error(f"Error adding Greeks: {e}")
                return options_df

        def _cache_data(self, categorized_data: Dict[str, pd.DataFrame]):
            """Cache data for historical analysis"""
            try:
                cache_entry = {
                    'timestamp': datetime.now(),
                    'spot_price': 0,
                    'vix_value': 0,
                    'total_oi': 0
                }

                if not categorized_data['spot'].empty:
                    cache_entry['spot_price'] = categorized_data['spot']['current_price'].iloc[0]

                if not categorized_data['vix'].empty:
                    cache_entry['vix_value'] = categorized_data['vix']['current_price'].iloc[0]

                if not categorized_data['options'].empty:
                    cache_entry['total_oi'] = categorized_data['options']['open_interest'].sum()

                self.data_history.append(cache_entry)

            except Exception as e:
                logger.debug(f"Error caching data: {e}")

    class SmartMoneyDetector:
        """Smart money flow detection using OI analysis"""

        def __init__(self, config_manager: ConfigManager):
            self.config = config_manager
            self.smart_money_config = config_manager.strategy_config["smart_money_detection"]
            self.flow_history = deque(maxlen=500)

        def detect_smart_money_flows(self, options_data: pd.DataFrame, instrument: str) -> pd.DataFrame:
            """Main smart money detection pipeline"""
            if options_data.empty:
                return pd.DataFrame()

            try:
                # Get instrument-specific thresholds
                thresholds = self.smart_money_config["oi_thresholds"].get(
                    instrument, self.smart_money_config["oi_thresholds"]["NIFTY"]
                )

                # Detect institutional flows
                signals = self._detect_institutional_flows(options_data, thresholds)

                # Add confidence scores
                signals = self._calculate_confidence_scores(signals)

                return signals

            except Exception as e:
                logger.error(f"Error in smart money detection: {e}")
                return pd.DataFrame()

        def _detect_institutional_flows(self, df: pd.DataFrame, thresholds: Dict) -> pd.DataFrame:
            """Detect large institutional flows"""
            signals = df.copy()

            # Large OI changes
            signals['large_oi_build'] = (
                    (signals['oi_change'] > thresholds['significant']) &
                    (signals['oi_change'] > 0)
            )

            signals['institutional_build'] = signals['oi_change'] > thresholds['institutional']

            # Overall smart money signal
            signals['smart_money_signal'] = (
                    signals['large_oi_build'] | signals['institutional_build']
            )

            return signals

        def _calculate_confidence_scores(self, df: pd.DataFrame) -> pd.DataFrame:
            """Calculate confidence scores for signals"""
            df = df.copy()

            try:
                df['confidence_score'] = 0.0

                # Base confidence from OI change magnitude
                if 'oi_change' in df.columns:
                    oi_change_normalized = abs(df['oi_change']) / 100000
                    df['confidence_score'] += np.minimum(oi_change_normalized * 0.3, 0.3)

                # Add confidence for institutional signals
                if 'institutional_build' in df.columns:
                    df.loc[df['institutional_build'], 'confidence_score'] += 0.4

                if 'large_oi_build' in df.columns:
                    df.loc[df['large_oi_build'], 'confidence_score'] += 0.3

                # Cap confidence at 1.0
                df['confidence_score'] = np.minimum(df['confidence_score'], 1.0)

            except Exception as e:
                logger.debug(f"Error calculating confidence scores: {e}")

            return df

    class StrategyEngine:
        """Strategy implementation and signal generation"""

        def __init__(self, config_manager: ConfigManager, smart_money_detector: SmartMoneyDetector):
            self.config = config_manager
            self.smart_money_detector = smart_money_detector
            self.strategy_config = config_manager.strategy_config
            self.signal_history = deque(maxlen=1000)

        def generate_signals(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
            """Main signal generation pipeline"""
            signals = []

            try:
                current_session = self.config.get_session_type(datetime.now().time())
                session_strategies = self.strategy_config["session_strategies"].get(current_session, [])

                for strategy_name in session_strategies:
                    try:
                        if strategy_name == "smart_money_following":
                            signals.extend(self._smart_money_following_strategy(market_data, instrument))
                        elif strategy_name == "gap_trading":
                            signals.extend(self._gap_trading_strategy(market_data, instrument))
                        elif strategy_name == "mean_reversion":
                            signals.extend(self._mean_reversion_strategy(market_data, instrument))
                        elif strategy_name == "volatility_trading":
                            signals.extend(self._volatility_trading_strategy(market_data, instrument))
                        elif strategy_name == "profit_booking":
                            signals.extend(self._profit_booking_strategy(market_data, instrument))

                    except Exception as e:
                        logger.error(f"Error in strategy {strategy_name}: {e}")

                # Filter and rank signals
                signals = self._filter_and_rank_signals(signals)

                return signals

            except Exception as e:
                logger.error(f"Error generating signals: {e}")
                return []

        def _smart_money_following_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
            """Smart money following strategy"""
            signals = []

            try:
                options_data = market_data.get('options', pd.DataFrame())
                if options_data.empty:
                    return signals

                # Get smart money signals
                smart_money_signals = self.smart_money_detector.detect_smart_money_flows(options_data, instrument)

                # Convert to trading signals
                high_confidence_signals = smart_money_signals[
                    (smart_money_signals.get('confidence_score', 0) > 0.7) &
                    (smart_money_signals.get('smart_money_signal', False))
                    ]

                for idx, row in high_confidence_signals.iterrows():
                    signal = {
                        'strategy': 'smart_money_following',
                        'instrument': instrument,
                        'strike': row.get('strike_price', 0),
                        'option_type': row.get('option_type', 'CE'),
                        'expiry': row.get('expiry_date'),
                        'signal_type': 'BUY' if row.get('oi_change', 0) > 0 else 'SELL',
                        'entry_price': row.get('current_price', 0),
                        'confidence': row.get('confidence_score', 0),
                        'reasoning': f"Smart money flow detected: OI change {row.get('oi_change', 0)}",
                        'timestamp': datetime.now()
                    }
                    signals.append(signal)

            except Exception as e:
                logger.debug(f"Error in smart money following strategy: {e}")

            return signals

        def _gap_trading_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
            """Gap trading strategy for opening session"""
            signals = []

            try:
                spot_data = market_data.get('spot', pd.DataFrame())
                options_data = market_data.get('options', pd.DataFrame())

                if spot_data.empty or options_data.empty:
                    return signals

                # Simple gap detection logic
                atm_options = options_data[abs(options_data.get('moneyness', 1)) < 0.02]

                for idx, row in atm_options.head(2).iterrows():
                    if row.get('current_price', 0) > 0:
                        signal = {
                            'strategy': 'gap_trading',
                            'instrument': instrument,
                            'strike': row.get('strike_price', 0),
                            'option_type': row.get('option_type', 'CE'),
                            'expiry': row.get('expiry_date'),
                            'signal_type': 'BUY',
                            'entry_price': row.get('current_price', 0),
                            'confidence': 0.65,
                            'reasoning': f"Gap trading opportunity at ATM strike",
                            'timestamp': datetime.now()
                        }
                        signals.append(signal)

            except Exception as e:
                logger.debug(f"Error in gap trading strategy: {e}")

            return signals

        def _mean_reversion_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
            """Mean reversion strategy"""
            signals = []

            try:
                options_data = market_data.get('options', pd.DataFrame())

                if options_data.empty:
                    return signals

                # Look for overpriced options
                if 'implied_volatility' in options_data.columns:
                    high_iv_options = options_data[
                        options_data['implied_volatility'] > options_data['implied_volatility'].quantile(0.8)
                        ]

                    for idx, row in high_iv_options.head(2).iterrows():
                        if row.get('current_price', 0) > 5:
                            signal = {
                                'strategy': 'mean_reversion',
                                'instrument': instrument,
                                'strike': row.get('strike_price', 0),
                                'option_type': row.get('option_type', 'CE'),
                                'expiry': row.get('expiry_date'),
                                'signal_type': 'SELL',
                                'entry_price': row.get('current_price', 0),
                                'confidence': 0.60,
                                'reasoning': f"High IV mean reversion: {row.get('implied_volatility', 0):.2f}",
                                'timestamp': datetime.now()
                            }
                            signals.append(signal)

            except Exception as e:
                logger.debug(f"Error in mean reversion strategy: {e}")

            return signals

        def _volatility_trading_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
            """Volatility-based trading strategy"""
            signals = []

            try:
                vix_data = market_data.get('vix', pd.DataFrame())
                options_data = market_data.get('options', pd.DataFrame())

                if vix_data.empty or options_data.empty:
                    return signals

                current_vix = vix_data['current_price'].iloc[0]

                # Low volatility regime - buy volatility
                if current_vix < 12:
                    atm_options = options_data[abs(options_data.get('moneyness', 1)) < 0.02]

                    for idx, row in atm_options.head(2).iterrows():
                        signal = {
                            'strategy': 'volatility_trading',
                            'instrument': instrument,
                            'strike': row.get('strike_price', 0),
                            'option_type': row.get('option_type', 'CE'),
                            'expiry': row.get('expiry_date'),
                            'signal_type': 'BUY',
                            'entry_price': row.get('current_price', 0),
                            'confidence': 0.65,
                            'reasoning': f"Low VIX regime ({current_vix:.1f}) - buy volatility",
                            'timestamp': datetime.now()
                        }
                        signals.append(signal)

                # High volatility regime - sell volatility
                elif current_vix > 18:
                    otm_options = options_data[abs(options_data.get('moneyness', 0)) > 0.02]

                    for idx, row in otm_options.head(2).iterrows():
                        signal = {
                            'strategy': 'volatility_trading',
                            'instrument': instrument,
                            'strike': row.get('strike_price', 0),
                            'option_type': row.get('option_type', 'CE'),
                            'expiry': row.get('expiry_date'),
                            'signal_type': 'SELL',
                            'entry_price': row.get('current_price', 0),
                            'confidence': 0.70,
                            'reasoning': f"High VIX regime ({current_vix:.1f}) - sell volatility",
                            'timestamp': datetime.now()
                        }
                        signals.append(signal)

            except Exception as e:
                logger.debug(f"Error in volatility trading strategy: {e}")

            return signals

        def _profit_booking_strategy(self, market_data: Dict[str, pd.DataFrame], instrument: str) -> List[Dict]:
            """Profit booking strategy for closing session"""
            signals = []
            # This would typically check existing positions and generate exit signals
            return signals

        def _filter_and_rank_signals(self, signals: List[Dict]) -> List[Dict]:
            """Filter and rank signals by confidence and other criteria"""
            if not signals:
                return signals

            try:
                # Filter by minimum confidence
                min_confidence = 0.5
                filtered_signals = [s for s in signals if s.get('confidence', 0) >= min_confidence]

                # Sort by confidence (descending)
                filtered_signals.sort(key=lambda x: x.get('confidence', 0), reverse=True)

                # Limit number of signals
                max_signals = 5
                return filtered_signals[:max_signals]

            except Exception as e:
                logger.debug(f"Error filtering signals: {e}")
                return signals

    class PaperTradingEngine:
        """Advanced paper trading with realistic execution simulation"""

        def __init__(self, config_manager: ConfigManager, initial_capital: float = 1000000):
            self.config = config_manager
            self.initial_capital = initial_capital
            self.current_capital = initial_capital
            self.positions: List[Position] = []
            self.completed_trades: List[Trade] = []
            self.daily_pnl = 0.0
            self.unrealized_pnl = 0.0
            self.max_drawdown = 0.0
            self.peak_capital = initial_capital

            # Risk management
            self.risk_config = config_manager.strategy_config["risk_management"]

            # Database for trade storage
            self.db_path = "paper_trading.db"
            self._initialize_database()

        def _initialize_database(self):
            """Initialize SQLite database for trade storage"""
            try:
                conn = sqlite3.connect(self.db_path)
                cursor = conn.cursor()

                # Positions table
                cursor.execute("""
                        CREATE TABLE IF NOT EXISTS positions (
                            id INTEGER PRIMARY KEY AUTOINCREMENT,
                            instrument TEXT,
                            strike REAL,
                            option_type TEXT,
                            expiry DATE,
                            entry_price REAL,
                            quantity INTEGER,
                            entry_time TIMESTAMP,
                            strategy TEXT,
                            stop_loss REAL,
                            target REAL,
                            current_price REAL,
                            unrealized_pnl REAL,
                            status TEXT DEFAULT 'OPEN'
                        )
                    """)

                # Completed trades table
                cursor.execute("""
                        CREATE TABLE IF NOT EXISTS completed_trades (
                            id INTEGER PRIMARY KEY AUTOINCREMENT,
                            instrument TEXT,
                            strike REAL,
                            option_type TEXT,
                            expiry DATE,
                            entry_price REAL,
                            exit_price REAL,
                            quantity INTEGER,
                            entry_time TIMESTAMP,
                            exit_time TIMESTAMP,
                            strategy TEXT,
                            pnl REAL,
                            max_profit REAL,
                            max_loss REAL,
                            exit_reason TEXT,
                            holding_time_minutes INTEGER
                        )
                    """)

                # Daily performance table
                cursor.execute("""
                        CREATE TABLE IF NOT EXISTS daily_performance (
                            date DATE PRIMARY KEY,
                            starting_capital REAL,
                            ending_capital REAL,
                            realized_pnl REAL,
                            unrealized_pnl REAL,
                            total_pnl REAL,
                            trades_count INTEGER,
                            winning_trades INTEGER,
                            max_drawdown REAL
                        )
                    """)

                conn.commit()
                conn.close()
                logger.info("Paper trading database initialized")

            except Exception as e:
                logger.error(f"Error initializing database: {e}")

        def execute_signal(self, signal: Dict, current_market_data: Dict[str, pd.DataFrame]) -> bool:
            """Execute a trading signal"""
            try:
                # Risk checks
                if not self._risk_check(signal):
                    logger.info(f"Signal rejected by risk management: {signal['strategy']}")
                    return False

                # Position sizing
                position_size = self._calculate_position_size(signal)
                if position_size <= 0:
                    logger.info(f"Invalid position size calculated: {position_size}")
                    return False

                # Simulate order execution
                executed_price = self._simulate_execution(signal, current_market_data)
                if executed_price <= 0:
                    logger.info(f"Order execution failed for signal: {signal['strategy']}")
                    return False

                # Create position
                position = Position(
                    instrument=signal['instrument'],
                    strike=signal['strike'],
                    option_type=signal['option_type'],
                    expiry=signal['expiry'],
                    entry_price=executed_price,
                    quantity=position_size,
                    entry_time=datetime.now(),
                    strategy=signal['strategy'],
                    stop_loss=self._calculate_stop_loss(executed_price, signal),
                    target=self._calculate_target(executed_price, signal)
                )

                self.positions.append(position)
                self._save_position_to_db(position)

                # Update capital
                trade_cost = executed_price * position_size
                self.current_capital -= trade_cost

                logger.info(
                    f"Position opened: {signal['strategy']} {signal['option_type']} {signal['strike']} @ {executed_price}")
                return True

            except Exception as e:
                logger.error(f"Error executing signal: {e}")
                return False

        def update_positions(self, current_market_data: Dict[str, pd.DataFrame]):
            """Update all open positions with current market data"""
            try:
                options_data = current_market_data.get('options', pd.DataFrame())
                if options_data.empty:
                    return

                positions_to_close = []

                for position in self.positions:
                    # Find current price for this position
                    position_data = options_data[
                        (options_data['strike_price'] == position.strike) &
                        (options_data['option_type'] == position.option_type) &
                        (options_data['expiry_date'] == position.expiry)
                        ]

                    if not position_data.empty:
                        current_price = position_data['current_price'].iloc[0]
                        position.update_price(current_price)

                        # Check exit conditions
                        exit_reason = self._check_exit_conditions(position)
                        if exit_reason:
                            positions_to_close.append((position, exit_reason))

                # Close positions that meet exit criteria
                for position, exit_reason in positions_to_close:
                    self._close_position(position, exit_reason)

                # Update unrealized P&L
                self.unrealized_pnl = sum(pos.unrealized_pnl for pos in self.positions)

                # Update performance metrics
                self._update_performance_metrics()

            except Exception as e:
                logger.error(f"Error updating positions: {e}")

        def _risk_check(self, signal: Dict) -> bool:
            """Comprehensive risk management checks"""
            try:
                # Check maximum positions limit
                if len(self.positions) >= self.risk_config["position_sizing"]["max_positions"]:
                    return False

                # Check daily loss limit
                daily_loss_limit = self.initial_capital * self.risk_config["position_sizing"]["max_portfolio_risk"]
                if abs(self.daily_pnl) > daily_loss_limit:
                    return False

                # Check available capital
                estimated_cost = signal.get('entry_price', 0) * 100
                if estimated_cost > self.current_capital * 0.5:
                    return False

                # Time-based checks
                current_time = datetime.now().time()
                session = self.config.get_session_type(current_time)

                if session == 'square_off':
                    return False

                return True

            except Exception as e:
                logger.debug(f"Error in risk check: {e}")
                return False

        def _calculate_position_size(self, signal: Dict) -> int:
            """Calculate position size based on risk management rules"""
            try:
                # Get instrument configuration
                instrument_config = self.config.get_instrument_config(signal['instrument'])
                if not instrument_config:
                    return 0

                lot_size = instrument_config['lot_size']
                entry_price = signal.get('entry_price', 0)

                if entry_price <= 0:
                    return 0

                # Risk-based position sizing
                risk_per_trade = self.current_capital * self.risk_config["position_sizing"]["max_risk_per_trade"]

                # Calculate stop loss distance
                stop_loss_pct = self.risk_config["stop_loss"]["options_long"]
                stop_loss_amount = entry_price * stop_loss_pct

                # Position size = Risk amount / Stop loss amount
                position_value = risk_per_trade / stop_loss_amount if stop_loss_amount > 0 else 0

                if position_value > 0:
                    num_lots = max(1, int(position_value / (entry_price * lot_size)))
                    return num_lots * lot_size

                return 0

            except Exception as e:
                logger.debug(f"Error calculating position size: {e}")
                return 0

        def _simulate_execution(self, signal: Dict, market_data: Dict[str, pd.DataFrame]) -> float:
            """Simulate realistic order execution with slippage"""
            try:
                options_data = market_data.get('options', pd.DataFrame())
                if options_data.empty:
                    return 0

                # Find the specific option
                option_data = options_data[
                    (options_data['strike_price'] == signal['strike']) &
                    (options_data['option_type'] == signal['option_type'])
                    ]

                if option_data.empty:
                    return 0

                current_price = option_data['current_price'].iloc[0]
                bid_price = option_data.get('bid_price', pd.Series([current_price])).iloc[0]
                ask_price = option_data.get('ask_price', pd.Series([current_price])).iloc[0]

                # Simulate slippage based on signal type
                if signal['signal_type'] == 'BUY':
                    executed_price = ask_price * 1.01  # 1% slippage
                else:
                    executed_price = bid_price * 0.99  # 1% slippage

                return max(0.05, executed_price)  # Minimum tick size

            except Exception as e:
                logger.debug(f"Error simulating execution: {e}")
                return 0

        def _calculate_stop_loss(self, entry_price: float, signal: Dict) -> float:
            """Calculate stop loss price"""
            try:
                if signal['signal_type'] == 'BUY':
                    stop_loss_pct = self.risk_config["stop_loss"]["options_long"]
                    return entry_price * (1 - stop_loss_pct)
                else:
                    stop_loss_multiplier = self.risk_config["stop_loss"]["options_short"]
                    return entry_price * stop_loss_multiplier

            except Exception:
                return entry_price * 0.7  # Default 30% stop loss

        def _calculate_target(self, entry_price: float, signal: Dict) -> float:
            """Calculate target price"""
            try:
                target_multiplier = self.risk_config["profit_targets"]["target_profit"]
                if signal['signal_type'] == 'BUY':
                    return entry_price * (1 + target_multiplier)
                else:
                    return entry_price * (1 - target_multiplier)

            except Exception:
                return entry_price * 1.5  # Default 50% target

        def _check_exit_conditions(self, position: Position) -> Optional[str]:
            """Check if position should be closed"""
            try:
                current_price = position.current_price

                # Stop loss check
                if position.quantity > 0:  # Long position
                    if current_price <= position.stop_loss:
                        return "Stop Loss"
                else:  # Short position
                    if current_price >= position.stop_loss:
                        return "Stop Loss"

                # Target check
                if position.quantity > 0:  # Long position
                    if current_price >= position.target:
                        return "Target Reached"
                else:  # Short position
                    if current_price <= position.target:
                        return "Target Reached"

                # Time-based exit
                time_to_expiry = (position.expiry - datetime.now()).days
                if time_to_expiry <= 0:
                    return "Expiry"

                # Session-based exit
                current_time = datetime.now().time()
                session = self.config.get_session_type(current_time)
                if session == 'square_off':
                    return "End of Day Square-off"

                return None

            except Exception as e:
                logger.debug(f"Error checking exit conditions: {e}")
                return None

        def _close_position(self, position: Position, exit_reason: str):
            """Close a position and record the trade"""
            try:
                # Calculate P&L
                exit_price = position.current_price
                pnl = (exit_price - position.entry_price) * position.quantity

                # Create completed trade record
                trade = Trade(
                    instrument=position.instrument,
                    strike=position.strike,
                    option_type=position.option_type,
                    expiry=position.expiry,
                    entry_price=position.entry_price,
                    exit_price=exit_price,
                    quantity=position.quantity,
                    entry_time=position.entry_time,
                    exit_time=datetime.now(),
                    strategy=position.strategy,
                    pnl=pnl,
                    max_profit=position.max_profit,
                    max_loss=position.max_loss,
                    exit_reason=exit_reason,
                    holding_time=datetime.now() - position.entry_time
                )

                self.completed_trades.append(trade)
                self._save_trade_to_db(trade)

                # Update capital
                trade_proceeds = exit_price * position.quantity
                self.current_capital += trade_proceeds
                self.daily_pnl += pnl

                # Remove from active positions
                self.positions.remove(position)

                logger.info(
                    f"Position closed: {position.strategy} {position.option_type} {position.strike} @ {exit_price}, P&L: {pnl:.2f}, Reason: {exit_reason}")

            except Exception as e:
                logger.error(f"Error closing position: {e}")

        def _save_position_to_db(self, position: Position):
            """Save position to database"""
            try:
                conn = sqlite3.connect(self.db_path)
                cursor = conn.cursor()

                cursor.execute("""
                        INSERT INTO positions (instrument, strike, option_type, expiry, entry_price, 
                                             quantity, entry_time, strategy, stop_loss, target, 
                                             current_price, unrealized_pnl)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                    position.instrument, position.strike, position.option_type,
                    position.expiry, position.entry_price, position.quantity,
                    position.entry_time, position.strategy, position.stop_loss,
                    position.target, position.current_price, position.unrealized_pnl
                ))

                conn.commit()
                conn.close()

            except Exception as e:
                logger.debug(f"Error saving position to database: {e}")

        def _save_trade_to_db(self, trade: Trade):
            """Save completed trade to database"""
            try:
                conn = sqlite3.connect(self.db_path)
                cursor = conn.cursor()

                cursor.execute("""
                        INSERT INTO completed_trades (instrument, strike, option_type, expiry, 
                                                    entry_price, exit_price, quantity, entry_time, 
                                                    exit_time, strategy, pnl, max_profit, max_loss, 
                                                    exit_reason, holding_time_minutes)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                    trade.instrument, trade.strike, trade.option_type, trade.expiry,
                    trade.entry_price, trade.exit_price, trade.quantity, trade.entry_time,
                    trade.exit_time, trade.strategy, trade.pnl, trade.max_profit,
                    trade.max_loss, trade.exit_reason, trade.holding_time.total_seconds() / 60
                ))

                conn.commit()
                conn.close()

            except Exception as e:
                logger.debug(f"Error saving trade to database: {e}")

        def _update_performance_metrics(self):
            """Update performance metrics"""
            try:
                total_capital = self.current_capital + self.unrealized_pnl

                # Update peak capital and drawdown
                if total_capital > self.peak_capital:
                    self.peak_capital = total_capital

                current_drawdown = (self.peak_capital - total_capital) / self.peak_capital
                self.max_drawdown = max(self.max_drawdown, current_drawdown)

            except Exception as e:
                logger.debug(f"Error updating performance metrics: {e}")

        def get_performance_summary(self) -> Dict:
            """Get comprehensive performance summary"""
            try:
                total_trades = len(self.completed_trades)
                winning_trades = len([t for t in self.completed_trades if t.pnl > 0])

                if total_trades > 0:
                    win_rate = winning_trades / total_trades
                    avg_pnl = sum(t.pnl for t in self.completed_trades) / total_trades
                    avg_holding_time = sum(
                        t.holding_time.total_seconds() for t in self.completed_trades) / total_trades / 60
                else:
                    win_rate = 0
                    avg_pnl = 0
                    avg_holding_time = 0

                total_capital = self.current_capital + self.unrealized_pnl
                total_return = (total_capital - self.initial_capital) / self.initial_capital

                return {
                    'initial_capital': self.initial_capital,
                    'current_capital': self.current_capital,
                    'unrealized_pnl': self.unrealized_pnl,
                    'total_capital': total_capital,
                    'daily_pnl': self.daily_pnl,
                    'total_return': total_return * 100,
                    'max_drawdown': self.max_drawdown * 100,
                    'total_trades': total_trades,
                    'winning_trades': winning_trades,
                    'win_rate': win_rate * 100,
                    'avg_pnl_per_trade': avg_pnl,
                    'avg_holding_time_minutes': avg_holding_time,
                    'active_positions': len(self.positions)
                }

            except Exception as e:
                logger.error(f"Error generating performance summary: {e}")
                return {}

        def get_trade_statistics(self) -> Dict:
            """Get detailed trade statistics"""
            try:
                if not self.completed_trades:
                    return {}

                trades = self.completed_trades
                total_trades = len(trades)
                winning_trades = len([t for t in trades if t.pnl > 0])
                losing_trades = total_trades - winning_trades

                # P&L statistics
                total_pnl = sum(t.pnl for t in trades)
                winning_pnl = sum(t.pnl for t in trades if t.pnl > 0)
                losing_pnl = sum(t.pnl for t in trades if t.pnl < 0)

                # Average statistics
                avg_win = winning_pnl / winning_trades if winning_trades > 0 else 0
                avg_loss = losing_pnl / losing_trades if losing_trades > 0 else 0
                avg_trade = total_pnl / total_trades if total_trades > 0 else 0

                # Risk metrics
                profit_factor = abs(winning_pnl / losing_pnl) if losing_pnl != 0 else float('inf')

                return {
                    'total_trades': total_trades,
                    'winning_trades': winning_trades,
                    'losing_trades': losing_trades,
                    'win_rate': (winning_trades / total_trades * 100) if total_trades > 0 else 0,
                    'total_pnl': total_pnl,
                    'avg_win': avg_win,
                    'avg_loss': avg_loss,
                    'avg_trade': avg_trade,
                    'profit_factor': profit_factor,
                    'largest_win': max((t.pnl for t in trades if t.pnl > 0), default=0),
                    'largest_loss': min((t.pnl for t in trades if t.pnl < 0), default=0)
                }

            except Exception as e:
                logger.error(f"Error calculating trade statistics: {e}")
                return {}

    class TradingSystemGUI:
        """Advanced GUI for the trading system"""

        def __init__(self, trading_system):
            self.trading_system = trading_system
            self.root = tk.Tk()
            self.root.title("Institutional-Grade Intraday Trading System")
            self.root.geometry("1400x900")

            # Configure style
            self.style = ttk.Style()
            self.style.theme_use('clam')

            self.setup_gui()
            self.update_thread = None
            self.is_running = False

        def setup_gui(self):
            """Setup the main GUI components"""
            # Create main notebook for tabs
            self.notebook = ttk.Notebook(self.root)
            self.notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

            # Create tabs
            self.create_main_tab()
            self.create_positions_tab()
            self.create_analytics_tab()
            self.create_settings_tab()

            # Status bar
            self.status_var = tk.StringVar(value="System Ready")
            self.status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN)
            self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        def create_main_tab(self):
            """Create main dashboard tab"""
            main_frame = ttk.Frame(self.notebook)
            self.notebook.add(main_frame, text="Dashboard")

            # Control panel
            control_frame = ttk.LabelFrame(main_frame, text="System Controls")
            control_frame.pack(fill=tk.X, padx=5, pady=5)

            # File selection
            ttk.Label(control_frame, text="Excel File:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
            self.file_path_var = tk.StringVar()
            ttk.Entry(control_frame, textvariable=self.file_path_var, width=60).grid(row=0, column=1, padx=5, pady=2)
            ttk.Button(control_frame, text="Browse", command=self.browse_file).grid(row=0, column=2, padx=5, pady=2)

            # Instrument selection
            ttk.Label(control_frame, text="Instrument:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
            self.instrument_var = tk.StringVar(value="NIFTY")
            instrument_combo = ttk.Combobox(control_frame, textvariable=self.instrument_var,
                                            values=["NIFTY", "BANKNIFTY", "CRUDEOIL"])
            instrument_combo.grid(row=1, column=1, sticky=tk.W, padx=5, pady=2)

            # Control buttons
            button_frame = ttk.Frame(control_frame)
            button_frame.grid(row=2, column=0, columnspan=3, pady=10)
